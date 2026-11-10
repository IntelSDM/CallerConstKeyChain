#include "CallerConstKeyPass.h"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/User.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <vector>

using namespace llvm;

llvm::cl::opt<bool> CallerConstKeyEnable("obfcallerconstkey", llvm::cl::init(true), llvm::cl::desc("Master Toggle"));

static constexpr unsigned MaxCascadeRounds = 8;
static constexpr bool EncConsts = true;
static constexpr bool EncStrings = true;
static constexpr bool EncGVPtrs = true;
static constexpr bool IndirectCalls = true;
static constexpr bool IndirectBranches = true;
static constexpr bool CascadeEnabled = true;

static constexpr uint64_t FNV1a64(const char* s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    while (*s)
    {
        h ^= (uint8_t)(*s);
        h *= 0x100000001b3ULL;
        ++s;
    }
    return h;
}

static uint64_t FNV1a64Range(StringRef s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    for (char c : s)
    {
        h ^= (uint8_t)c;
        h *= 0x100000001b3ULL;
    }
    return h;
}

struct ConstArg
{
    unsigned paramidx;
    unsigned bitwidth;
    uint64_t value;
};

struct SiteRecord
{
    CallBase* call = nullptr;
    Function* caller = nullptr;
    Function* callee = nullptr;
    uint64_t foldedkey = 0;
    SmallVector<ConstArg, 4> consts;
    bool needsinjection = false;
    Value* parentruntimekey = nullptr;
};

static std::vector<SiteRecord> gEligibleSites;
static DenseMap<Function*, unsigned> gCloneCounter;
static DenseMap<Function*, Function*> gCloneOrigin;
static DenseMap<Function*, DenseMap<unsigned, uint64_t>> gKeyedArgsValues;
static DenseMap<Function*, Instruction*> gKeyDiffAddPerClone;

static bool IsCRTSpecial(StringRef n)
{
    if (n.starts_with("_tls_callback")) return true;
    switch (FNV1a64Range(n))
    {
        case FNV1a64("DllMain"):
        case FNV1a64("_DllMainCRTStartup"):
        case FNV1a64("DllMainCRTStartup"):
        case FNV1a64("mainCRTStartup"):
        case FNV1a64("wmainCRTStartup"):
        case FNV1a64("WinMainCRTStartup"):
        case FNV1a64("wWinMainCRTStartup"):
        case FNV1a64("_CRT_INIT"):
        case FNV1a64("__scrt_common_main"):
        case FNV1a64("__scrt_common_main_seh"):
        case FNV1a64("__scrt_dllmain_before_initialize_c"):
        case FNV1a64("__scrt_dllmain_after_initialize_c"):
            return true;
    }
    return false;
}

static bool IsCompilerHelper(StringRef n)
{
    if (n.starts_with("__GSHandlerCheck")) return true;
    if (n.starts_with("_RTC_")) return true;
    if (n.starts_with("__scrt_")) return true;
    if (n.starts_with("__acrt_")) return true;
    if (n.starts_with("__crt_")) return true;
    switch (FNV1a64Range(n))
    {
        case FNV1a64("_chkstk"):
        case FNV1a64("__chkstk"):
        case FNV1a64("__chkstk_ms"):
        case FNV1a64("__security_check_cookie"):
        case FNV1a64("__security_init_cookie"):
        case FNV1a64("__CxxFrameHandler3"):
        case FNV1a64("__CxxFrameHandler4"):
        case FNV1a64("__C_specific_handler"):
        case FNV1a64("__CxxThrowException"):
        case FNV1a64("__std_terminate"):
        case FNV1a64("__std_exception_copy"):
        case FNV1a64("__std_exception_destroy"):
        case FNV1a64("__RTDynamicCast"):
        case FNV1a64("__RTtypeid"):
        case FNV1a64("__RTCastToVoid"):
        case FNV1a64("_purecall"):
        case FNV1a64("__purecall"):
        case FNV1a64("__report_rangecheckfailure"):
        case FNV1a64("__report_securityfailure"):
        case FNV1a64("_Init_thread_header"):
        case FNV1a64("_Init_thread_footer"):
        case FNV1a64("_Init_thread_abort"):
        case FNV1a64("_Init_thread_epoch"):
        case FNV1a64("__msvc_align"):
            return true;
    }
    return false;
}

static bool IsOurHelper(StringRef n)
{
    return n.starts_with("__cck_");
}

static bool IsVTableGV(StringRef n)
{
    if (n.starts_with("??_7")) return true;
    if (n.starts_with("??_R4")) return true;
    if (n.starts_with("_ZTV")) return true;
    if (n.starts_with("_ZTC")) return true;
    if (n.starts_with("_ZTT")) return true;
    return false;
}

static void CollectGlobalCtorDtorFuncs(Module& m, DenseSet<Function*>& out)
{
    const StringRef tables[] = {"llvm.global_ctors", "llvm.global_dtors"};
    for (StringRef tn : tables)
    {
        GlobalVariable* gv = m.getNamedGlobal(tn);
        if (!gv || !gv->hasInitializer()) continue;
        auto* ca = dyn_cast<ConstantArray>(gv->getInitializer());
        if (!ca) continue;
        for (unsigned i = 0; i < ca->getNumOperands(); ++i)
        {
            auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
            if (!cs || cs->getNumOperands() < 2) continue;
            Value* v = cs->getOperand(1)->stripPointerCasts();
            if (auto* f = dyn_cast<Function>(v)) out.insert(f);
        }
    }
}

static void CollectFunctionsFromConstant(Constant* c, DenseSet<Function*>& out, DenseSet<Constant*>& visited)
{
    if (!c) return;
    if (!visited.insert(c).second) return;
    if (auto* f = dyn_cast<Function>(c)) { out.insert(f); return; }
    for (unsigned i = 0, n = c->getNumOperands(); i < n; ++i)
        if (auto* sub = dyn_cast<Constant>(c->getOperand(i)))
            CollectFunctionsFromConstant(sub, out, visited);
}

static void CollectVTableFuncs(Module& m, DenseSet<Function*>& out)
{
    DenseSet<Constant*> visited;
    for (GlobalVariable& gv : m.globals())
    {
        if (!gv.hasInitializer()) continue;
        if (!IsVTableGV(gv.getName())) continue;
        CollectFunctionsFromConstant(gv.getInitializer(), out, visited);
    }
}

static bool UserLeadsOnlyToMetadataGlobals(User* u, DenseSet<User*>& visited)
{
    if (!visited.insert(u).second) return true;
    if (auto* gv = dyn_cast<GlobalVariable>(u))
    {
        StringRef n = gv->getName();
        switch (FNV1a64Range(n))
        {
            case FNV1a64("llvm.global.annotations"):
            case FNV1a64("llvm.used"):
            case FNV1a64("llvm.compiler.used"):
            case FNV1a64("llvm.metadata"):
                return true;
        }
        return false;
    }
    if (isa<Instruction>(u)) return false;
    if (u->user_empty()) return false;
    for (User* uu : u->users())
        if (!UserLeadsOnlyToMetadataGlobals(uu, visited))
            return false;
    return true;
}

static bool DetectAddressTaken(Function& f)
{
    for (User* u : f.users())
    {
        if (auto* cb = dyn_cast<CallBase>(u))
        {
            if (cb->getCalledOperand() != &f) return true;
            continue;
        }
        DenseSet<User*> visited;
        if (!UserLeadsOnlyToMetadataGlobals(u, visited)) return true;
    }
    return false;
}

static bool HasAnnotationTag(Function& f, const char* tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga || !ga->hasInitializer()) return false;
    auto* ca = dyn_cast<ConstantArray>(ga->getOperand(0));
    if (!ca) return false;
    for (unsigned i = 0; i < ca->getNumOperands(); ++i)
    {
        auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs || cs->getNumOperands() < 2) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;
        auto* annogv = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!annogv || !annogv->hasInitializer()) continue;
        auto* cds = dyn_cast<ConstantDataSequential>(annogv->getInitializer());
        if (!cds || !cds->isString()) continue;
        StringRef s = cds->getAsString();
        if (s.starts_with(tag) && s.size() == strlen(tag) + 1) return true;
    }
    return false;
}

static bool HasNoCallerConstKeyAnnotation(Function& f)
{
    return HasAnnotationTag(f, "nocallerconstkey");
}

static Function* ResolveCallee(CallBase* cb)
{
    if (Function* f = cb->getCalledFunction()) return f;
    Value* v = cb->getCalledOperand();
    if (!v) return nullptr;
    v = v->stripPointerCasts();
    for (unsigned i = 0; i < 8; ++i)
    {
        auto* ga = dyn_cast<GlobalAlias>(v);
        if (!ga) break;
        Constant* aliasee = ga->getAliasee();
        if (!aliasee) break;
        v = aliasee->stripPointerCasts();
    }
    return dyn_cast<Function>(v);
}

static bool ShapeOK(CallBase* cb)
{
    if (cb->isInlineAsm()) return false;
    if (isa<CallBrInst>(cb)) return false;
    if (isa<InvokeInst>(cb)) return false;
    if (auto* ci = dyn_cast<CallInst>(cb))
        if (ci->isMustTailCall()) return false;
    Function* callee = ResolveCallee(cb);
    if (!callee) return false;
    if (callee->isIntrinsic()) return false;
    return true;
}

static bool CalleeOK(Function* f, const DenseSet<Function*>& ctordtorset)
{
    if (!f) return false;
    if (f->isDeclaration()) return false;
    if (IsOurHelper(f->getName())) return false;
    if (f->hasFnAttribute(Attribute::Naked)) return false;
    if (IsCRTSpecial(f->getName())) return false;
    if (IsCompilerHelper(f->getName())) return false;
    if (ctordtorset.contains(f)) return false;
    if (HasNoCallerConstKeyAnnotation(*f)) return false;
    return true;
}

static bool ClassifyContent(CallBase* cb, Function* callee, SiteRecord& rec)
{
    if (!callee) return false;
    const unsigned nfixed = callee->getFunctionType()->getNumParams();
    if (nfixed == 0) return false;
    const unsigned nargs = std::min<unsigned>(cb->arg_size(), nfixed);
    for (unsigned pi = 0; pi < nargs; ++pi)
    {
        Value* op = cb->getArgOperand(pi);
        auto* ci = dyn_cast<ConstantInt>(op);
        if (!ci) continue;
        unsigned bw = ci->getBitWidth();
        if (bw != 8 && bw != 16 && bw != 32 && bw != 64) continue;
        ConstArg a;
        a.paramidx = pi;
        a.bitwidth = bw;
        a.value = ci->getZExtValue();
        rec.consts.push_back(a);
        rec.foldedkey += a.value;
    }
    return !rec.consts.empty();
}

static void MarkCCK(Instruction* i)
{
    if (!i) return;
    if (i->getMetadata("cck.r1")) return;
    i->setMetadata("cck.r1", MDNode::get(i->getContext(), {}));
}

static Function* CloneCalleeForSite(Function* callee, const Twine& suffix)
{
    Function* clone = Function::Create(callee->getFunctionType(), GlobalValue::InternalLinkage, callee->getAddressSpace(), callee->getName() + ".cck" + suffix, callee->getParent());
    clone->copyAttributesFrom(callee);
    clone->setLinkage(GlobalValue::InternalLinkage);
    clone->setUnnamedAddr(GlobalValue::UnnamedAddr::Local);
    clone->setCallingConv(callee->getCallingConv());
    clone->addFnAttr(Attribute::NoInline);
    clone->removeFnAttr(Attribute::AlwaysInline);
    clone->removeFnAttr(Attribute::InlineHint);
    clone->addFnAttr("cck-site-clone");
    ValueToValueMapTy vmap;
    auto oit = callee->arg_begin();
    auto nit = clone->arg_begin();
    for (; oit != callee->arg_end(); ++oit, ++nit)
    {
        nit->setName(oit->getName());
        vmap[&*oit] = &*nit;
    }
    SmallVector<ReturnInst*, 4> returns;
    CloneFunctionInto(clone, callee, vmap, CloneFunctionChangeType::LocalChangesOnly, returns);
    return clone;
}

static Function* CloneCalleeForSiteWithInjection(Function* callee, const Twine& suffix)
{
    LLVMContext& c = callee->getContext();
    FunctionType* oldft = callee->getFunctionType();
    SmallVector<Type*, 8> newparams(oldft->params().begin(), oldft->params().end());
    newparams.push_back(Type::getInt64Ty(c));
    FunctionType* newft = FunctionType::get(oldft->getReturnType(), newparams, oldft->isVarArg());
    Function* clone = Function::Create(newft, GlobalValue::InternalLinkage, callee->getAddressSpace(), callee->getName() + ".cck" + suffix, callee->getParent());
    clone->copyAttributesFrom(callee);
    clone->setLinkage(GlobalValue::InternalLinkage);
    clone->setUnnamedAddr(GlobalValue::UnnamedAddr::Local);
    clone->setCallingConv(callee->getCallingConv());
    clone->addFnAttr(Attribute::NoInline);
    clone->removeFnAttr(Attribute::AlwaysInline);
    clone->removeFnAttr(Attribute::InlineHint);
    clone->addFnAttr("cck-site-clone");
    clone->addFnAttr("cck-injected-key");
    ValueToValueMapTy vmap;
    auto oit = callee->arg_begin();
    auto nit = clone->arg_begin();
    for (; oit != callee->arg_end(); ++oit, ++nit)
    {
        nit->setName(oit->getName());
        vmap[&*oit] = &*nit;
    }
    nit->setName("__cck_key");
    SmallVector<ReturnInst*, 4> returns;
    CloneFunctionInto(clone, callee, vmap, CloneFunctionChangeType::LocalChangesOnly, returns);
    return clone;
}

static CallInst* RewriteCallWithExtraArg(CallBase* oldcb, Function* newclone, Value* extraarg)
{
    IRBuilder<> b(oldcb);
    LLVMContext& c = oldcb->getContext();
    FunctionType* newft = newclone->getFunctionType();
    unsigned insertat = newft->getNumParams() - 1;
    SmallVector<Value*, 8> newargs(oldcb->args().begin(), oldcb->args().end());
    AttributeList oldattrs = oldcb->getAttributes();
    SmallVector<AttributeSet, 8> newparamattrs;
    newparamattrs.reserve(newargs.size() + 1);
     for variadic callees the injected key must land at the LAST fixed slot not past the variadic data args, otherwise the key operand misaligns with the fixed i64 param and the verifier rejects the call
    if (insertat >= newargs.size())
    {
        for (unsigned i = 0; i < newargs.size(); ++i)
            newparamattrs.push_back(oldattrs.getParamAttrs(i));
        newargs.push_back(extraarg);
        newparamattrs.push_back(AttributeSet());
    }
    else
    {
        for (unsigned i = 0; i < insertat; ++i)
            newparamattrs.push_back(oldattrs.getParamAttrs(i));
        newparamattrs.push_back(AttributeSet());
        for (unsigned i = insertat; i < newargs.size(); ++i)
            newparamattrs.push_back(oldattrs.getParamAttrs(i));
        newargs.insert(newargs.begin() + insertat, extraarg);
    }
    CallInst* newci = b.CreateCall(newft, newclone, newargs);
    newci->setCallingConv(oldcb->getCallingConv());
    if (auto* oldci = dyn_cast<CallInst>(oldcb))
        newci->setTailCallKind(oldci->getTailCallKind());
    AttributeList newattrlist = AttributeList::get(c, oldattrs.getFnAttrs(), oldattrs.getRetAttrs(), newparamattrs);
    newci->setAttributes(newattrlist);
    newci->setDebugLoc(oldcb->getDebugLoc());
    if (!oldcb->getType()->isVoidTy())
    {
        newci->takeName(oldcb);
        oldcb->replaceAllUsesWith(newci);
    }
    oldcb->eraseFromParent();
    return newci;
}

static Value* EmitParentRuntimeKeyAt(Function* parent, Instruction* insertbefore)
{
    LLVMContext& c = parent->getContext();
    Type* i64 = Type::getInt64Ty(c);
    IRBuilder<> b(insertbefore);
    auto it = gKeyedArgsValues.find(parent);
    if (it == gKeyedArgsValues.end() || it->second.empty())
        return ConstantInt::get(i64, 0);
    Value* k = ConstantInt::get(i64, 0);
    for (auto& kv : it->second)
    {
        Argument* argp = parent->getArg(kv.first);
        Value* zext;
        if (argp->getType()->isIntegerTy(64))
        {
            zext = argp;
        }
        else if (argp->getType()->isIntegerTy())
        {
            auto* z = cast<Instruction>(b.CreateZExt(argp, i64, "PZ64"));
            MarkCCK(z);
            zext = z;
        }
        else
        {
            continue;
        }
        auto* addi = cast<Instruction>(b.CreateAdd(k, zext, "PSum"));
        MarkCCK(addi);
        k = addi;
    }
    return k;
}

static bool CloneHasFunclets(Function* clone)
{
    for (BasicBlock& bb : *clone)
        for (Instruction& i : bb)
            if (isa<FuncletPadInst>(&i) || isa<CatchReturnInst>(&i) || isa<CleanupReturnInst>(&i))
                return true;
    return false;
}

static bool IsCCKEncryptableInstr(Instruction* i)
{
    if (i->getMetadata("cck.r1")) return false;
    if (isa<PHINode>(i)) return false;
    if (isa<GetElementPtrInst>(i)) return false;
    if (isa<SwitchInst>(i)) return false;
    if (isa<AllocaInst>(i)) return false;
    if (isa<ExtractValueInst>(i)) return false;
    if (isa<InsertValueInst>(i)) return false;
    if (isa<LandingPadInst>(i)) return false;
    if (isa<FuncletPadInst>(i)) return false;
    if (isa<CatchReturnInst>(i)) return false;
    if (isa<CleanupReturnInst>(i)) return false;
    if (isa<ResumeInst>(i)) return false;
    if (auto* cb = dyn_cast<CallBase>(i))
    {
        if (cb->isInlineAsm()) return false;
        if (cb->getIntrinsicID() != Intrinsic::not_intrinsic) return false;
    }
    return true;
}

static bool IsCCKOperandData(Instruction* i, unsigned opidx)
{
    if (auto* cb = dyn_cast<CallBase>(i))
    {
        if (opidx >= cb->arg_size()) return false;
        if (cb->paramHasAttr(opidx, Attribute::ImmArg)) return false;
        return true;
    }
    if (isa<StoreInst>(i))
    {
        if (opidx != 0) return false;
        return true;
    }
    if (isa<LoadInst>(i)) return false;
    if (isa<AtomicRMWInst>(i))
    {
        if (opidx != 1) return false;
        return true;
    }
    if (isa<AtomicCmpXchgInst>(i))
    {
        if (opidx != 1 && opidx != 2) return false;
        return true;
    }
    return true;
}

static uint64_t CCKGen64()
{
    uint64_t a = (uint64_t)(rand() & 0xFFFF);
    uint64_t b = (uint64_t)(rand() & 0xFFFF);
    uint64_t c = (uint64_t)(rand() & 0xFFFF);
    uint64_t d = (uint64_t)(rand() & 0xFFFF);
    return a | (b << 16) | (c << 32) | (d << 48);
}

static bool ShouldEncryptCloneGV(GlobalVariable* gv)
{
    if (!gv) return false;
    if (gv->getName().starts_with("llvm.")) return false;
    if (gv->getName().starts_with("__cck_")) return false;
    if (gv->isThreadLocal()) return false;
    if (gv->isConstant() && gv->hasInitializer())
    {
        if (auto* arrt = dyn_cast<ArrayType>(gv->getValueType()))
        {
            Type* elemt = arrt->getElementType();
            if ((elemt->isIntegerTy(8) || elemt->isIntegerTy(16)) && isa<ConstantDataSequential>(gv->getInitializer()))
                return false;
        }
    }
    return true;
}

static void EncryptCloneStrings(Function* clone, Value* keydiffadd, Instruction* anchor)
{
    LLVMContext& c = clone->getContext();
    Type* i64 = Type::getInt64Ty(c);
    DenseSet<GlobalVariable*> seen;
    SmallVector<GlobalVariable*, 16> entries;
    for (BasicBlock& bb : *clone)
    {
        for (Instruction& i : bb)
        {
            if (i.getMetadata("cck.r1")) continue;
            for (unsigned oi = 0, oe = i.getNumOperands(); oi != oe; ++oi)
            {
                Value* op = i.getOperand(oi);
                Value* stripped = op;
                while (auto* gep = dyn_cast<GEPOperator>(stripped))
                    stripped = gep->getPointerOperand();
                auto* gv = dyn_cast<GlobalVariable>(stripped);
                if (!gv || !gv->isConstant() || !gv->hasInitializer()) continue;
                auto* arrt = dyn_cast<ArrayType>(gv->getValueType());
                if (!arrt) continue;
                Type* elemt = arrt->getElementType();
                if (!elemt->isIntegerTy(8) && !elemt->isIntegerTy(16)) continue;
                auto* init = dyn_cast<ConstantDataSequential>(gv->getInitializer());
                if (!init) continue;
                if (!seen.insert(gv).second) continue;
                entries.push_back(gv);
            }
        }
    }
    if (entries.empty()) return;
    for (GlobalVariable* gv : entries)
    {
        auto* init = cast<ConstantDataSequential>(gv->getInitializer());
        auto* arrt = cast<ArrayType>(gv->getValueType());
        unsigned ebits = arrt->getElementType()->getIntegerBitWidth();
        unsigned esize = ebits / 8;
        unsigned nelems = init->getNumElements();
        unsigned total = nelems * esize;
        unsigned padded = ((total + 7) / 8) * 8;
        unsigned nchunks = padded / 8;
        unsigned elemsperchunk = 8 / esize;
        unsigned nchunksaligned = (nchunks + 1u) & ~1u;
        IRBuilder<> be(&clone->getEntryBlock(), clone->getEntryBlock().begin());
        AllocaInst* slot = be.CreateAlloca(i64, ConstantInt::get(i64, nchunksaligned), "StrBuf");
        slot->setAlignment(Align(16));
        MarkCCK(slot);
        IRBuilder<> bd(anchor->getParent(), std::next(anchor->getIterator()));
        for (unsigned chunkidx = 0; chunkidx < nchunks; ++chunkidx)
        {
            uint64_t plain = 0;
            for (unsigned k = 0; k < elemsperchunk; ++k)
            {
                unsigned elemidx = chunkidx * elemsperchunk + k;
                if (elemidx >= nelems) break;
                uint64_t v = init->getElementAsInteger(elemidx);
                plain |= v << (k * ebits);
            }
            uint64_t mask = CCKGen64();
            uint64_t cipherct = plain + mask;
            Value* effmask = bd.CreateAdd(ConstantInt::get(i64, mask), keydiffadd, "StrEMask");
            Value* dec = bd.CreateSub(ConstantInt::get(i64, cipherct), effmask, "StrDec");
            Value* dst = bd.CreateGEP(i64, slot, ConstantInt::get(i64, chunkidx), "StrDst");
            auto* st = bd.CreateStore(dec, dst);
            if (auto* di = dyn_cast<Instruction>(effmask)) MarkCCK(di);
            if (auto* di = dyn_cast<Instruction>(dec)) MarkCCK(di);
            if (auto* di = dyn_cast<Instruction>(dst)) MarkCCK(di);
            MarkCCK(st);
        }
        SmallVector<Use*, 8> toreplace;
        for (Use& u : gv->uses())
        {
            auto* useri = dyn_cast<Instruction>(u.getUser());
            if (!useri) continue;
            if (useri->getFunction() != clone) continue;
            if (useri->getMetadata("cck.r1")) continue;
            toreplace.push_back(&u);
        }
        for (Use* u : toreplace) u->set(slot);
    }
}

static void EncryptCloneGVPtrs(Function* clone, Value* keydiffadd, Instruction* anchor)
{
    LLVMContext& c = clone->getContext();
    Module* m = clone->getParent();
    Type* i64 = Type::getInt64Ty(c);
    PointerType* ptrty = PointerType::get(c, 0);
    DenseSet<GlobalVariable*> seen;
    SmallVector<GlobalVariable*, 16> gvs;
    for (BasicBlock& bb : *clone)
    {
        for (Instruction& i : bb)
        {
            if (i.getMetadata("cck.r1")) continue;
            for (unsigned oi = 0, oe = i.getNumOperands(); oi != oe; ++oi)
            {
                auto* gv = dyn_cast<GlobalVariable>(i.getOperand(oi));
                if (!ShouldEncryptCloneGV(gv)) continue;
                if (!seen.insert(gv).second) continue;
                gvs.push_back(gv);
            }
        }
    }
    if (gvs.empty()) return;
    Instruction* insertafter = anchor;
    for (GlobalVariable* gv : gvs)
    {
        uint64_t mask = CCKGen64();
        Constant* addr = ConstantExpr::getPtrToInt(gv, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        Constant* enc = ConstantExpr::getAdd(addr, maskc);
        auto* holder = new GlobalVariable(*m, i64, false, GlobalValue::PrivateLinkage, enc, "__cck_gv_ref");
        holder->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
        IRBuilder<> b(insertafter->getParent(), std::next(insertafter->getIterator()));
        Value* loaded = b.CreateLoad(i64, holder, "GVLoad");
        Value* effmask = b.CreateAdd(maskc, keydiffadd, "GVEMask");
        Value* dec = b.CreateSub(loaded, effmask, "GVDec");
        Value* ptr = b.CreateIntToPtr(dec, ptrty, "GVP");
        if (auto* di = dyn_cast<Instruction>(loaded)) MarkCCK(di);
        if (auto* di = dyn_cast<Instruction>(effmask)) MarkCCK(di);
        if (auto* di = dyn_cast<Instruction>(dec)) MarkCCK(di);
        if (auto* di = dyn_cast<Instruction>(ptr)) MarkCCK(di);
        SmallVector<Use*, 8> toreplace;
        for (Use& u : gv->uses())
        {
            auto* useri = dyn_cast<Instruction>(u.getUser());
            if (!useri) continue;
            if (useri->getFunction() != clone) continue;
            if (useri->getMetadata("cck.r1")) continue;
            toreplace.push_back(&u);
        }
        for (Use* u : toreplace) u->set(ptr);
        insertafter = cast<Instruction>(ptr);
    }
}

static void IndirectCloneCalls(Function* clone, Value* keydiffadd)
{
    LLVMContext& c = clone->getContext();
    Module* m = clone->getParent();
    Type* i64 = Type::getInt64Ty(c);
    PointerType* ptrty = PointerType::get(c, 0);
    SmallVector<std::pair<CallBase*, Function*>, 32> toindirect;
    for (BasicBlock& bb : *clone)
    {
        for (Instruction& i : bb)
        {
            if (i.getMetadata("cck.r1")) continue;
            auto* call = dyn_cast<CallBase>(&i);
            if (!call) continue;
            if (isa<CallBrInst>(call)) continue;
            if (call->isInlineAsm()) continue;
            if (auto* ci = dyn_cast<CallInst>(call))
                if (ci->isMustTailCall()) continue;
            Function* callee = call->getCalledFunction();
            if (!callee) continue;
            if (callee->isIntrinsic()) continue;
            if (callee->getName().starts_with("__cck_")) continue;
            if (IsCompilerHelper(callee->getName())) continue;
            if (IsCRTSpecial(callee->getName())) continue;
            if (callee->getFunctionType() != call->getFunctionType()) continue;
            toindirect.push_back({call, callee});
        }
    }
    for (auto& t : toindirect)
    {
        CallBase* call = t.first;
        Function* callee = t.second;
        uint64_t mask = CCKGen64();
        Constant* addr = ConstantExpr::getPtrToInt(callee, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        Constant* enc = ConstantExpr::getAdd(addr, maskc);
        auto* holder = new GlobalVariable(*m, i64, false, GlobalValue::PrivateLinkage, enc, "__cck_ind_call");
        holder->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
        IRBuilder<> b(call);
        Value* loaded = b.CreateLoad(i64, holder, "CeeLoad");
        Value* effmask = b.CreateAdd(maskc, keydiffadd, "CeeEMask");
        Value* dec = b.CreateSub(loaded, effmask, "CeeDec");
        Value* fn = b.CreateIntToPtr(dec, ptrty, "CeeP");
        if (auto* di = dyn_cast<Instruction>(loaded)) MarkCCK(di);
        if (auto* di = dyn_cast<Instruction>(effmask)) MarkCCK(di);
        if (auto* di = dyn_cast<Instruction>(dec)) MarkCCK(di);
        if (auto* di = dyn_cast<Instruction>(fn)) MarkCCK(di);
        call->setCalledOperand(fn);
    }
}

static void IndirectCloneBranches(Function* clone, Value* keydiffadd)
{
    LLVMContext& c = clone->getContext();
    Module* m = clone->getParent();
    Type* i64 = Type::getInt64Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    PointerType* ptrty = PointerType::get(c, 0);
    SmallVector<BranchInst*, 32> toindirect;
    DenseMap<BasicBlock*, unsigned> tgtidx;
    SmallVector<BasicBlock*, 32> tgtordered;
    for (BasicBlock& bb : *clone)
    {
        auto* br = dyn_cast<BranchInst>(bb.getTerminator());
        if (!br) continue;
        if (br->getMetadata("cck.r1")) continue;
        bool hasehsucc = false;
        for (BasicBlock* succ : br->successors())
            if (succ && succ->isEHPad()) { hasehsucc = true; break; }
        if (hasehsucc) continue;
        toindirect.push_back(br);
        for (BasicBlock* succ : br->successors())
            if (tgtidx.insert({succ, (unsigned)tgtordered.size()}).second)
                tgtordered.push_back(succ);
    }
    if (toindirect.empty()) return;
    unsigned n = tgtordered.size();
    ArrayType* at = ArrayType::get(i64, n);
    SmallVector<Constant*, 32> addrentries(n);
    SmallVector<Constant*, 32> maskentries(n);
    for (unsigned i = 0; i < n; ++i)
    {
        uint64_t mask = CCKGen64();
        Constant* ba = BlockAddress::get(clone, tgtordered[i]);
        Constant* baint = ConstantExpr::getPtrToInt(ba, i64);
        Constant* maskc = ConstantInt::get(i64, mask);
        addrentries[i] = ConstantExpr::getAdd(baint, maskc);
        maskentries[i] = maskc;
    }
    auto* addrtable = new GlobalVariable(*m, at, false, GlobalValue::PrivateLinkage, ConstantArray::get(at, addrentries), "__cck_ind_br_addrtbl");
    addrtable->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    auto* masktable = new GlobalVariable(*m, at, false, GlobalValue::PrivateLinkage, ConstantArray::get(at, maskentries), "__cck_ind_br_masktbl");
    masktable->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    Constant* zero32 = ConstantInt::get(i32, 0);
    for (BranchInst* br : toindirect)
    {
        IRBuilder<> b(br);
        Value* idx;
        if (br->isConditional())
        {
            Constant* idxt = ConstantInt::get(i32, tgtidx[br->getSuccessor(0)]);
            Constant* idxf = ConstantInt::get(i32, tgtidx[br->getSuccessor(1)]);
            idx = b.CreateSelect(br->getCondition(), idxt, idxf, "BrIdx");
        }
        else
        {
            idx = ConstantInt::get(i32, tgtidx[br->getSuccessor(0)]);
        }
        Value* agep = b.CreateGEP(at, addrtable, {zero32, idx}, "BrAGep");
        Value* mgep = b.CreateGEP(at, masktable, {zero32, idx}, "BrMGep");
        Value* loaded = b.CreateLoad(i64, agep, "BrLoad");
        Value* mask = b.CreateLoad(i64, mgep, "BrMask");
        Value* effmask = b.CreateAdd(mask, keydiffadd, "BrEMask");
        Value* dec = b.CreateSub(loaded, effmask, "BrDec");
        Value* tgt = b.CreateIntToPtr(dec, ptrty, "BrP");
        if (auto* di = dyn_cast<Instruction>(idx)) MarkCCK(di);
        if (auto* di = dyn_cast<Instruction>(agep)) MarkCCK(di);
        if (auto* di = dyn_cast<Instruction>(mgep)) MarkCCK(di);
        if (auto* di = dyn_cast<Instruction>(loaded)) MarkCCK(di);
        if (auto* di = dyn_cast<Instruction>(mask)) MarkCCK(di);
        if (auto* di = dyn_cast<Instruction>(effmask)) MarkCCK(di);
        if (auto* di = dyn_cast<Instruction>(dec)) MarkCCK(di);
        if (auto* di = dyn_cast<Instruction>(tgt)) MarkCCK(di);
        SmallVector<BasicBlock*, 2> succs;
        for (BasicBlock* sc : br->successors()) succs.push_back(sc);
        auto* ibr = IndirectBrInst::Create(tgt, succs.size(), br);
        for (BasicBlock* sc : succs) ibr->addDestination(sc);
        ibr->copyMetadata(*br);
        MarkCCK(ibr);
        br->eraseFromParent();
    }
}

static void EncryptCloneBody(Function* clone, const SiteRecord& rec)
{
    LLVMContext& c = clone->getContext();
    Type* i64 = Type::getInt64Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    BasicBlock& entry = clone->getEntryBlock();
    IRBuilder<> b(&*entry.getFirstInsertionPt());
    Value* k = ConstantInt::get(i64, 0);
    for (const ConstArg& a : rec.consts)
    {
        Argument* argp = clone->getArg(a.paramidx);
        Value* zext;
        if (a.bitwidth == 64)
        {
            zext = argp;
        }
        else
        {
            auto* z = cast<Instruction>(b.CreateZExt(argp, i64, "Z64"));
            MarkCCK(z);
            zext = z;
        }
        auto* addi = cast<Instruction>(b.CreateAdd(k, zext, "KSum"));
        MarkCCK(addi);
        k = addi;
    }
    uint64_t kct = 0;
    for (const ConstArg& a : rec.consts) kct += a.value;
    Value* k32;
    {
        auto* t = cast<Instruction>(b.CreateTrunc(k, i32, "K32"));
        MarkCCK(t);
        k32 = t;
    }
    Instruction* keydiffadd;
    {
        auto* d = cast<Instruction>(b.CreateSub(k, ConstantInt::get(i64, kct), "KeyDiff"));
        MarkCCK(d);
        keydiffadd = d;
    }
    gKeyDiffAddPerClone[clone] = keydiffadd;
    SmallVector<std::pair<Instruction*, unsigned>, 32> targets;
    for (BasicBlock& bb : *clone)
    {
        for (Instruction& i : bb)
        {
            if (i.getMetadata("cck.r1")) continue;
            if (!IsCCKEncryptableInstr(&i)) continue;
            for (unsigned oi = 0, oe = i.getNumOperands(); oi != oe; ++oi)
            {
                auto* ci = dyn_cast<ConstantInt>(i.getOperand(oi));
                if (!ci) continue;
                unsigned bw = ci->getBitWidth();
                if (bw != 32 && bw != 64) continue;
                if (!IsCCKOperandData(&i, oi)) continue;
                targets.push_back({&i, oi});
            }
        }
    }
    for (auto& t : targets)
    {
        Instruction* i = t.first;
        unsigned opidx = t.second;
        auto* ci = cast<ConstantInt>(i->getOperand(opidx));
        unsigned bw = ci->getBitWidth();
        IRBuilder<> ib(i);
        if (bw == 64)
        {
            uint64_t v = ci->getZExtValue();
            uint64_t ciph = v ^ kct;
            auto* dec = cast<Instruction>(ib.CreateXor(ConstantInt::get(i64, ciph), k, "Dec"));
            MarkCCK(dec);
            i->setOperand(opidx, dec);
        }
        else
        {
            uint32_t v = (uint32_t)ci->getZExtValue();
            uint32_t ciph = v ^ (uint32_t)(kct & 0xFFFFFFFFu);
            auto* dec = cast<Instruction>(ib.CreateXor(ConstantInt::get(i32, ciph), k32, "Dec32"));
            MarkCCK(dec);
            i->setOperand(opidx, dec);
        }
    }
    // indirect call phase MUST stay deferred to the post cascade sweep; running it per clone here misses direct calls inserted by later cascade rounds into this already encrypted body
    if (EncStrings) EncryptCloneStrings(clone, keydiffadd, keydiffadd);
    if (EncGVPtrs) EncryptCloneGVPtrs(clone, keydiffadd, keydiffadd);
    if (IndirectBranches) IndirectCloneBranches(clone, keydiffadd);
}

static void ScanFnForCascadeSites(Function* f, const DenseSet<Function*>& ctordtorset, std::vector<SiteRecord>& out)
{
    if (!f || f->isDeclaration()) return;
    Function* origin = nullptr;
    {
        auto it = gCloneOrigin.find(f);
        if (it != gCloneOrigin.end()) origin = it->second;
    }
    uint64_t parentkct = 0;
    auto kit = gKeyedArgsValues.find(f);
    if (kit != gKeyedArgsValues.end())
        for (auto& kv : kit->second)
            parentkct += kv.second;
    for (BasicBlock& bb : *f)
    {
        for (Instruction& i : bb)
        {
            auto* cb = dyn_cast<CallBase>(&i);
            if (!cb) continue;
            if (!ShapeOK(cb)) continue;
            Function* callee = ResolveCallee(cb);
            if (!CalleeOK(callee, ctordtorset)) continue;
            if (origin && callee == origin) continue;
            const unsigned trailingidx = callee->getFunctionType()->getNumParams();
            SiteRecord rec;
            rec.call = cb;
            rec.caller = f;
            rec.callee = callee;
            rec.foldedkey = parentkct;
            rec.needsinjection = true;
            rec.parentruntimekey = nullptr;
            ConstArg a;
            a.paramidx = trailingidx;
            a.bitwidth = 64;
            a.value = parentkct;
            rec.consts.push_back(a);
            out.push_back(rec);
        }
    }
}

static bool RunCloneAndEncrypt(Module& m, const DenseSet<Function*>& ctordtorset)
{
    (void)m;
    gCloneCounter.clear();
    gCloneOrigin.clear();
    gKeyedArgsValues.clear();
    gKeyDiffAddPerClone.clear();
    const unsigned maxrounds = CascadeEnabled ? MaxCascadeRounds : 1u;
    DenseSet<Function*> calleesevercloned;
    std::vector<SiteRecord> worksites = gEligibleSites;
    unsigned sitescloned = 0;
    for (unsigned round = 1; round <= maxrounds; ++round)
    {
        if (worksites.empty()) break;
        std::vector<Function*> newclonesthisround;
        newclonesthisround.reserve(worksites.size());
        std::vector<SiteRecord> nextsites;
        for (SiteRecord& rec : worksites)
        {
            Function* callee = rec.callee;
            unsigned siteid = gCloneCounter[callee]++;
            Function* clone;
            if (rec.needsinjection)
                clone = CloneCalleeForSiteWithInjection(callee, Twine(siteid));
            else
                clone = CloneCalleeForSite(callee, Twine(siteid));
            if (!clone) continue;
            gCloneOrigin[clone] = callee;
            if (!rec.consts.empty())
            {
                auto& kam = gKeyedArgsValues[clone];
                for (const ConstArg& a : rec.consts)
                    kam[a.paramidx] = a.value;
            }
            auto* oldcb = const_cast<CallBase*>(rec.call);
            if (rec.needsinjection)
            {
                Function* parent = oldcb->getFunction();
                Value* parentk = EmitParentRuntimeKeyAt(parent, oldcb);
                RewriteCallWithExtraArg(oldcb, clone, parentk);
            }
            else
            {
                oldcb->setCalledOperand(clone);
            }
            ++sitescloned;
            calleesevercloned.insert(callee);
            // cascade scan MUST run before encrypting this clone; after encryption direct calls become inttoptr indirections, ResolveCallee returns null, and the subtree is lost
            if (CascadeEnabled && round < maxrounds)
                ScanFnForCascadeSites(clone, ctordtorset, nextsites);
            if (EncConsts && !rec.consts.empty())
            {
                if (!CloneHasFunclets(clone))
                    EncryptCloneBody(clone, rec);
            }
            newclonesthisround.push_back(clone);
        }
        worksites = std::move(nextsites);
    }
    if (IndirectCalls)
    {
        for (auto& kv : gCloneOrigin)
        {
            Function* clone = kv.first;
            if (!clone || clone->isDeclaration()) continue;
            if (CloneHasFunclets(clone)) continue;
            auto it = gKeyDiffAddPerClone.find(clone);
            if (it == gKeyDiffAddPerClone.end()) continue;
            Instruction* keydiffadd = it->second;
            if (!keydiffadd) continue;
            if (keydiffadd->getParent() == nullptr || keydiffadd->getFunction() != clone) continue;
            IndirectCloneCalls(clone, keydiffadd);
        }
    }
    return sitescloned > 0;
}

bool RunCallerConstKey(Module& m)
{
    if (!CallerConstKeyEnable) return false;
    gEligibleSites.clear();
    DenseSet<Function*> ctordtorset;
    CollectGlobalCtorDtorFuncs(m, ctordtorset);
    DenseSet<Function*> vtableset;
    CollectVTableFuncs(m, vtableset);
    for (Function& f : m)
    {
        if (f.isDeclaration()) continue;
        for (BasicBlock& bb : f)
        {
            for (Instruction& i : bb)
            {
                auto* cb = dyn_cast<CallBase>(&i);
                if (!cb) continue;
                if (!ShapeOK(cb)) continue;
                Function* callee = ResolveCallee(cb);
                if (!CalleeOK(callee, ctordtorset)) continue;
                SiteRecord rec;
                rec.call = cb;
                rec.caller = &f;
                rec.callee = callee;
                if (!ClassifyContent(cb, callee, rec)) continue;
                gEligibleSites.push_back(rec);
            }
        }
    }
    return RunCloneAndEncrypt(m, ctordtorset);
}

PreservedAnalyses CallerConstKeyPass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunCallerConstKey(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}
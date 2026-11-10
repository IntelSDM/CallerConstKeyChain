# Caller Const Key Pass
Built for LLVM 19.1 - Windows x64 <br> <br>

This is a component of Nessa's homomorphism engine.<br> 
The idea is quite simple, Certain function calls will pass constants through them. <br>
```c
int Add(int a, int b)
{
return a+b;
}
int Mult(int a, int b)
{
return a*b;
}

void Example()
{
const int val1 = Add(10,20);
const int val2 = Mult(100,1);
}
```

So here for example we have 10,20 as parameters to `Add` and 100,1 as parameters to `Mult`. <br>
Lets say example is called by Func5, which has a call graph of
```
Func1 -> Func2 -> Func3 -> Func4 -> Func5 -> Example
```
We would take those constants 10,20,100,1 and move them all the way up to func1. Then we clone (make xrefless copies of the function) all the functions in the path and make new ones pass the parameters down. <br>
So Func1 loads the constants, each Function is then going to take the parameter(as it is a new single xref function, specially made for this call chain), passing it through each function until it hits example. <br>
Then to example these were loaded AGES ago, so each function was just passing the pointer, the actual value was loaded long ago. This means if you only have example, you need to reverse engineer up to Func1 to get the constants. <br>
So you just follow the call graph right? Well Nessa uses the other homomorphism systems and just flat out encrypts and indirects all calls. There is no call graph. <br>
Example doesn't know what these constants are, but we do. So we use them as an encryption key. <br>

### Loading Constants
<img width="852" height="509" alt="image" src="https://github.com/user-attachments/assets/4ad09398-e127-4675-995e-19878505d866" /> <br>

### Pass them down

<img width="747" height="115" alt="image" src="https://github.com/user-attachments/assets/ec62a59d-d81b-4192-b049-ced05f3d41b2" /> <br>
<img width="645" height="688" alt="image" src="https://github.com/user-attachments/assets/1108d5f3-443d-4708-b729-07b0afd843e3" /> <br>


## How To Build
* Download [LLVM 19.1](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.0)
* Download [VCPKG](https://github.com/microsoft/vcpkg)
* VCPKG install asmjit
* Open build.bat in a text editor.
* Find the LLVM 19.1 references in the command line, Change them to your file path.
* Find the VCPKG references in the command line, Change them to your file path.
* Run the build script
* Build your application with the ``` -load-pass-plugin ``` Param to the FunctionPass.dll

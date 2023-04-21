运行方式：
    cd build
    cmake --build .
    cd ..
    ./Inv <input file> (或者是 ./run_inv 一次性运行Benchmark目录下面所有文件)

编译的细节都写在Cmakelist.txt里面，如果有不懂的可以问我。
控制流跳转上面，还有两种跳转(基于逻辑运算符,dowhile跳转)没有写处理，但这个比较easy，所以没急于补。

以下是llvm-17的环境配置，写在我另外一个文档里面，我就复制到这里来了：

### **Important Environment**

我们使用以下指令来为我们的环境配置必要的库文件。注意，在运行命令之前，请确保之前未安装过相关版本的clang[防止版本冲突，但实际上估计影响不大]，本次项目使用clang-17,llvm-17，请注意命令使用的顺序不要随意改变。

方法适用：Vmware WorkStation Pro (Newest Version) + Ubuntu20.04LTS

```
wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key 
sudo apt-key add -
sudo add-apt-repository "deb http://apt.llvm.org/focal/ llvm-toolchain-focal main"
sudo apt-get update
sudo apt install libclang-dev
sudo apt-get install clang
sudo apt-get install llvm
```


> 备注：因为用指令安装的libclang-dev会在/usr/lib/x86_64...目录下自动添加一个失效软链接，而实际上我们所需要使用的动态库or静态库文件都在/usr/lib/llvm-17/lib/目录下面，而这个目录下面使用sudo apt-get install自动安装里面，libclang.so和libclang17.so都指向/usr/lib/x86_64...目录下的一个不存在的文件，并未指向实际的libclang17动态库文件。因此需要手动修改软链接，查找到x86_64目录下面的实际文件之后，将llvm-17/lib下面的软链接修改到实际的目录下面。

【有一些具体的细节我也忘了，这个是我大概按照我处理的流程回忆写下来的，里面的一些细节比较琐碎。】
【Cmake可能需要根据你所使用的具体环境稍作修改，比如include的位置，有部分include我写死了，这个估计之后等项目快交付的时候我会考虑不同环境的影响，写死的主要是CXX_flags下面的-I命令，Cmake里面应该可以看得到】
【如果有什么问题的话，方便交流可以加微信:think_of_life，有相关的技术问题我也可以请教一下。如果平时比较忙的话，那就主要在双周会议的时候交流。】
【以上。】
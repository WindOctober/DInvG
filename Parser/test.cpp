#include"clang-c/Index.h"
using namespace std;
int main(){
    CXIndex idx;
    idx=clang_createIndex(1,1);
    return 0;
}

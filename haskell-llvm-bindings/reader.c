#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

//#define __STDC_LIMIT_MACROS
//#define __STDC_CONSTANT_MACROS
#include <llvm-c/BitReader.h>
#include <llvm-c/Core.h>

int main(int argc, char** argv) {
    printf("Hello world\n");

    LLVMMemoryBufferRef buf =0;
    char* msg;
    LLVMModuleRef module = 0;

    const char* path="main.bc";

    if (LLVMCreateMemoryBufferWithContentsOfFile(path, &buf, &msg)) {
	fprintf(stderr, "Failed to open %s:\n  %s\n", path, msg);
	LLVMDisposeMessage(msg);
	exit(-1);
    }

    if (LLVMParseBitcode(buf, &module, &msg)) {
	fprintf(stderr, "Failed to parse bitcode: %s\n", msg);
	LLVMDisposeMessage(msg);
	LLVMDisposeMemoryBuffer(buf);
	exit(-1);
    }
    LLVMDisposeMemoryBuffer(buf);

    printf("Data layout: %s\n", LLVMGetDataLayout(module));
    printf("Target:      %s\n", LLVMGetTarget(module));
    LLVMDumpModule(module);


    LLVMValueRef fn = LLVMGetFirstFunction(module);
    while (fn != 0) {
	printf("Function %s\n", LLVMGetValueName(fn));
	LLVMTypeRef type = LLVMTypeOf(fn);

	unsigned cnt = LLVMCountBasicBlocks(fn);


	fn = LLVMGetNextFunction(fn);
    }

    /*
    LLVMValueRef global = LLVMGetFirstGlobal(module);
    while (global != 0) {
	printf("Global %s\n", LLVMGetValueName(global));
	global = LLBMGetNextGlobal(global);
    }
    */


    LLVMDisposeModule(module);
    return 0;
}

//
// This file was generated by the Retargetable Decompiler
// Website: https://retdec.com
// Copyright (c) 2020 Retargetable Decompiler <info@retdec.com>
//

#include <assert.h>
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>

// --------------------- Global Variables ---------------------

int32_t g1 = 0; // 0x601058
int32_t g2 = 0; // 0x60105c
int32_t g3;

// ------------------------ Functions -------------------------

// Address range: 0x40075e - 0x4008ca
int main(int argc, char ** argv) {
    // 0x40075e
    int64_t thread; // bp-40
    pthread_create((int32_t *)&thread, NULL, (int64_t * (*)(int64_t *))0x4006a6, NULL);
    int64_t thread2; // bp-32
    pthread_create((int32_t *)&thread2, NULL, (int64_t * (*)(int64_t *))0x4006ba, (int64_t *)1);
    int64_t thread3; // bp-24
    pthread_create((int32_t *)&thread3, NULL, (int64_t * (*)(int64_t *))0x4006ce, NULL);
    int64_t thread4; // bp-16
    pthread_create((int32_t *)&thread4, NULL, (int64_t * (*)(int64_t *))0x400716, (int64_t *)1);
    pthread_join((int32_t)thread, NULL);
    pthread_join((int32_t)thread2, NULL);
    pthread_join((int32_t)thread3, NULL);
    pthread_join((int32_t)thread4, NULL);
    if (g1 == 1 == g2 == 1) {
        goto lab_0x400880;
    } else {
        if (g1 == 2 == g2 == 2) {
            goto lab_0x400880;
        } else {
            goto lab_0x400899;
        }
    }
  lab_0x400880:
    // 0x400880
    __assert_fail("! ((a==1 && b==1) || (a==2 && b==2))", "add.c", 62, "main");
    goto lab_0x400899;
  lab_0x400899:;
    int64_t result;
    if (g2 == 1 != (g1 == 1)) {
        // 0x4008af
        __assert_fail("a==1 && b==1", "add.c", 63, "main");
        result = &g3;
    } else {
        result = 1;
    }
    // 0x4008c8
    return result;
}

// --------------- Dynamically Linked Functions ---------------

// void __assert_fail(const char * assertion, const char * file, unsigned int line, const char * function);
// int pthread_create(pthread_t * restrict newthread, const pthread_attr_t * restrict attr, void *(* start_routine)(void *), void * restrict arg);
// int pthread_join(pthread_t th, void ** thread_return);

// --------------------- Meta-Information ---------------------

// Detected compiler/packer: gcc (4.9.4)
// Detected functions: 1
// Decompilation date: 2020-02-10 16:32:05

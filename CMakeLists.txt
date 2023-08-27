cmake_minimum_required(VERSION 3.4.3)
project(relax-inv-gen)

#===============================================================================
# 1. LOAD LLVM CONFIGURATION
#===============================================================================
# Set this to a valid LLVM installation dir
set(LT_LLVM_INSTALL_DIR "" CACHE PATH "LLVM installation directory")

# Add the location of LLVMConfig.cmake to CMake search paths (so that
# find_package can locate it)
list(APPEND CMAKE_PREFIX_PATH "${LT_LLVM_INSTALL_DIR}/lib/cmake/llvm/")

find_package(LLVM 12.0.0 REQUIRED CONFIG)
find_package(Z3 REQUIRED CONFIG)
  #REQUIRED
 # CONFIG
  # `NO_DEFAULT_PATH` is set so that -DZ3_DIR has to be passed to find Z3.
  # This should prevent us from accidentally picking up an installed
  # copy of Z3. This is here to benefit Z3's build system when building
  # this project. When making your own project you probably shouldn't
  # use this option.
  # NO_DEFAULT_PATH
#)

message(STATUS "Z3_FOUND: ${Z3_FOUND}")
message(STATUS "Found Z3 ${Z3_VERSION_STRING}")
message(STATUS "Z3_DIR: ${Z3_DIR}")

# HelloWorld includes headers from LLVM - update the include paths accordingly
include_directories(SYSTEM ${LLVM_INCLUDE_DIRS})

#===============================================================================
# 2. LLVM-TUTOR BUILD CONFIGURATION
#===============================================================================
# Use the same C++ standard as LLVM does
set(CMAKE_CXX_STANDARD 14 CACHE STRING "")

# LLVM is normally built without RTTI. Be consistent with that.
if(NOT LLVM_ENABLE_RTTI)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")
endif()

#===============================================================================
# 3. ADD THE TARGET
#===============================================================================
add_library(MainAnalysis SHARED MainAnalysis.cpp ThreadDetails.cpp ThreadLocalStorage.cpp Order.cpp)

# Allow undefined symbols in shared objects on Darwin (this is the default
# behaviour on Linux)
#target_link_libraries(MainAnalysis "$<$<PLATFORM_ID:Darwin>:-undefined dynamic_lookup>" ${Z3_LIBRARIES})
target_include_directories(MainAnalysis PRIVATE ${Z3_C_INCLUDE_DIRS})
target_link_libraries(MainAnalysis PRIVATE ${Z3_LIBRARIES})

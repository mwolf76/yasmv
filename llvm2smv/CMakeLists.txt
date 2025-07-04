cmake_minimum_required(VERSION 3.10)
project(llvm2smv)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find LLVM
find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

# Set LLVM header and library paths
include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

# Include our headers
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/include)

# Main executable
add_executable(llvm2smv
    src/main.cpp
    src/LLVM2SMVPass.cpp
    src/TypeTranslator.cpp
    src/ExprTranslator.cpp
    src/SMVWriter.cpp
)

# Link against LLVM libraries
llvm_map_components_to_libnames(llvm_libs
    core
    irreader
    support
    passes
    analysis
    bitwriter
    transformutils
)

target_link_libraries(llvm2smv ${llvm_libs})

# Install targets
install(TARGETS llvm2smv DESTINATION bin)

# Example files
install(DIRECTORY examples/ DESTINATION share/llvm2smv/examples)

cmake_minimum_required(VERSION 2.8.12)
project(incremental_pidgeon_hole_principle)

# You can use the cmake builtin 'cmake -LH' to list all options.

# Options
set(USER_CXX_FLAGS "" CACHE STRING "Use this variable to provide additional\
flags to the compiler.")
set(IPASIR_DIR "${CMAKE_SOURCE_DIR}/external/lib/ipasir" CACHE STRING
"The directory which contains one or more implemntations to the ipasir \
interface. The libs should have the format 'libipasir[solver-name].a'")
set(BUILD_TESTS "ON" CACHE STRING
"Whether to build tests. Values: ON, OFF")

# Basic Settings
set(CMAKE_CXX_FLAGS "-std=c++14 -O3 -Wall -Wextra -Wpedantic -pthread -g ${USER_CXX_FLAGS}")
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static-libstdc++")
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/bin)
set(CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/external/cmake")

include_directories(${CMAKE_SOURCE_DIR}/src)
include_directories(${CMAKE_SOURCE_DIR}/external/include)

set(SRC_FILES
		src/carj/carj.cpp
		src/incphp.cpp
	)

set(UNIT_TEST_FILES
		test/TestBasic.cpp
		test/TestSatVariable.cpp
	)

add_library(ipasir_wrapper external/include/ipasir/ipasir_cpp.cpp)
add_library(all_sources ${SRC_FILES})

if (BUILD_TESTS EQUAL "ON")
	# Include google test, our testing framework
	include(gtest)

	# === Target: unitTest ===
	add_executable(unitTest ${UNIT_TEST_FILES})
	target_link_libraries(unitTest
		all_sources
		ipasir_wrapper
		gtest_main
		gmock_main
	)
	set_target_properties(unitTest PROPERTIES
		COTIRE_PREFIX_HEADER_IGNORE_PATH "${CMAKE_SOURCE_DIR}"
			_PREFIX_HEADER_INCLUDE_PATH "${CMAKE_SOURCE_DIR}/libs")
else()
	add_custom_target(unitTest)
endif()

# === Target: runtest ===
add_custom_target(runTest
	COMMAND ./unitTest --gtest_color=yes
	WORKING_DIRECTORY ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}
	DEPENDS unitTest)

# === Target: incphp-[solver_name] ===

# Creates executables for each aviable solver [solver-name]

# This folder should contain the library of solvers to link aigainst. Each
# incremental solver library should be named libipasir[solver-name].a
get_filename_component(IPASIR_DIR_ABS ${IPASIR_DIR} ABSOLUTE)
file(GLOB ipasir_libs RELATIVE ${IPASIR_DIR_ABS}
	${IPASIR_DIR_ABS}/libipasir*.a
	)

message(STATUS "Found the following libs in ${IPASIR_DIR_ABS}: ${ipasir_libs}")
FOREACH(ipasir_lib ${ipasir_libs})
	message(STATUS "${ipasir_lib}")
ENDFOREACH()

FOREACH(ipasir_lib ${ipasir_libs})
	string(REGEX REPLACE "libipasir(.*).a" "\\1" libname ${ipasir_lib})
	add_executable(incphp-${libname} src/main.cpp)
	target_link_libraries(incphp-${libname}
		all_sources
		ipasir_wrapper
		${IPASIR_DIR_ABS}/${ipasir_lib}
		)
ENDFOREACH()

# === Target: core ===

# Dummy target which builds all targets but only for one solver
add_custom_target(core DEPENDS unitTest runTest)
if (TARGET incphp-gmod)
	add_dependencies(core incphp-gmod)

	# Make sure the tool is build, even if tests fail.
	add_dependencies(runTest incphp-gmod)
endif()

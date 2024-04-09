# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.28

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /root/relic-submission

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /root/relic-submission/target-x64-pbc-fm18-768

# Include any dependencies generated for this target.
include bench/CMakeFiles/bench_epx.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include bench/CMakeFiles/bench_epx.dir/compiler_depend.make

# Include the progress variables for this target.
include bench/CMakeFiles/bench_epx.dir/progress.make

# Include the compile flags for this target's objects.
include bench/CMakeFiles/bench_epx.dir/flags.make

bench/CMakeFiles/bench_epx.dir/bench_epx.c.o: bench/CMakeFiles/bench_epx.dir/flags.make
bench/CMakeFiles/bench_epx.dir/bench_epx.c.o: /root/relic-submission/bench/bench_epx.c
bench/CMakeFiles/bench_epx.dir/bench_epx.c.o: bench/CMakeFiles/bench_epx.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --progress-dir=/root/relic-submission/target-x64-pbc-fm18-768/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building C object bench/CMakeFiles/bench_epx.dir/bench_epx.c.o"
	cd /root/relic-submission/target-x64-pbc-fm18-768/bench && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -MD -MT bench/CMakeFiles/bench_epx.dir/bench_epx.c.o -MF CMakeFiles/bench_epx.dir/bench_epx.c.o.d -o CMakeFiles/bench_epx.dir/bench_epx.c.o -c /root/relic-submission/bench/bench_epx.c

bench/CMakeFiles/bench_epx.dir/bench_epx.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Preprocessing C source to CMakeFiles/bench_epx.dir/bench_epx.c.i"
	cd /root/relic-submission/target-x64-pbc-fm18-768/bench && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /root/relic-submission/bench/bench_epx.c > CMakeFiles/bench_epx.dir/bench_epx.c.i

bench/CMakeFiles/bench_epx.dir/bench_epx.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Compiling C source to assembly CMakeFiles/bench_epx.dir/bench_epx.c.s"
	cd /root/relic-submission/target-x64-pbc-fm18-768/bench && /usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /root/relic-submission/bench/bench_epx.c -o CMakeFiles/bench_epx.dir/bench_epx.c.s

# Object files for target bench_epx
bench_epx_OBJECTS = \
"CMakeFiles/bench_epx.dir/bench_epx.c.o"

# External object files for target bench_epx
bench_epx_EXTERNAL_OBJECTS =

bin/bench_epx: bench/CMakeFiles/bench_epx.dir/bench_epx.c.o
bin/bench_epx: bench/CMakeFiles/bench_epx.dir/build.make
bin/bench_epx: lib/librelic_s.a
bin/bench_epx: /usr/lib/libgmp.a
bin/bench_epx: bench/CMakeFiles/bench_epx.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --bold --progress-dir=/root/relic-submission/target-x64-pbc-fm18-768/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking C executable ../bin/bench_epx"
	cd /root/relic-submission/target-x64-pbc-fm18-768/bench && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/bench_epx.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
bench/CMakeFiles/bench_epx.dir/build: bin/bench_epx
.PHONY : bench/CMakeFiles/bench_epx.dir/build

bench/CMakeFiles/bench_epx.dir/clean:
	cd /root/relic-submission/target-x64-pbc-fm18-768/bench && $(CMAKE_COMMAND) -P CMakeFiles/bench_epx.dir/cmake_clean.cmake
.PHONY : bench/CMakeFiles/bench_epx.dir/clean

bench/CMakeFiles/bench_epx.dir/depend:
	cd /root/relic-submission/target-x64-pbc-fm18-768 && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /root/relic-submission /root/relic-submission/bench /root/relic-submission/target-x64-pbc-fm18-768 /root/relic-submission/target-x64-pbc-fm18-768/bench /root/relic-submission/target-x64-pbc-fm18-768/bench/CMakeFiles/bench_epx.dir/DependInfo.cmake "--color=$(COLOR)"
.PHONY : bench/CMakeFiles/bench_epx.dir/depend


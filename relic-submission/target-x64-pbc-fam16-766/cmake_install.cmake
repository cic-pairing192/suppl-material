# Install script for directory: /root/relic-submission

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/usr/local")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "")
  endif()
  message(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
endif()

# Set the component getting installed.
if(NOT CMAKE_INSTALL_COMPONENT)
  if(COMPONENT)
    message(STATUS "Install component: \"${COMPONENT}\"")
    set(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  else()
    set(CMAKE_INSTALL_COMPONENT)
  endif()
endif()

# Install shared libraries without execute permission?
if(NOT DEFINED CMAKE_INSTALL_SO_NO_EXE)
  set(CMAKE_INSTALL_SO_NO_EXE "0")
endif()

# Is this installation the result of a crosscompile?
if(NOT DEFINED CMAKE_CROSSCOMPILING)
  set(CMAKE_CROSSCOMPILING "FALSE")
endif()

# Set default install directory permissions.
if(NOT DEFINED CMAKE_OBJDUMP)
  set(CMAKE_OBJDUMP "/usr/bin/objdump")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/relic" TYPE FILE FILES
    "/root/relic-submission/include/relic.h"
    "/root/relic-submission/include/relic_alloc.h"
    "/root/relic-submission/include/relic_arch.h"
    "/root/relic-submission/include/relic_bc.h"
    "/root/relic-submission/include/relic_bench.h"
    "/root/relic-submission/include/relic_bn.h"
    "/root/relic-submission/include/relic_core.h"
    "/root/relic-submission/include/relic_cp.h"
    "/root/relic-submission/include/relic_dv.h"
    "/root/relic-submission/include/relic_eb.h"
    "/root/relic-submission/include/relic_ec.h"
    "/root/relic-submission/include/relic_ed.h"
    "/root/relic-submission/include/relic_ep.h"
    "/root/relic-submission/include/relic_epx.h"
    "/root/relic-submission/include/relic_err.h"
    "/root/relic-submission/include/relic_fb.h"
    "/root/relic-submission/include/relic_fbx.h"
    "/root/relic-submission/include/relic_fp.h"
    "/root/relic-submission/include/relic_fpx.h"
    "/root/relic-submission/include/relic_label.h"
    "/root/relic-submission/include/relic_md.h"
    "/root/relic-submission/include/relic_mpc.h"
    "/root/relic-submission/include/relic_multi.h"
    "/root/relic-submission/include/relic_pc.h"
    "/root/relic-submission/include/relic_pp.h"
    "/root/relic-submission/include/relic_rand.h"
    "/root/relic-submission/include/relic_test.h"
    "/root/relic-submission/include/relic_types.h"
    "/root/relic-submission/include/relic_util.h"
    )
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/relic/low" TYPE FILE FILES
    "/root/relic-submission/include/low/relic_bn_low.h"
    "/root/relic-submission/include/low/relic_dv_low.h"
    "/root/relic-submission/include/low/relic_fb_low.h"
    "/root/relic-submission/include/low/relic_fp_low.h"
    "/root/relic-submission/include/low/relic_fpx_low.h"
    )
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/relic" TYPE DIRECTORY FILES "/root/relic-submission/target-x64-pbc-fam16-766/include/")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/cmake" TYPE FILE FILES "/root/relic-submission/cmake/relic-config.cmake")
endif()

if(NOT CMAKE_INSTALL_LOCAL_ONLY)
  # Include the install script for each subdirectory.
  include("/root/relic-submission/target-x64-pbc-fam16-766/src/cmake_install.cmake")
  include("/root/relic-submission/target-x64-pbc-fam16-766/test/cmake_install.cmake")
  include("/root/relic-submission/target-x64-pbc-fam16-766/bench/cmake_install.cmake")

endif()

if(CMAKE_INSTALL_COMPONENT)
  set(CMAKE_INSTALL_MANIFEST "install_manifest_${CMAKE_INSTALL_COMPONENT}.txt")
else()
  set(CMAKE_INSTALL_MANIFEST "install_manifest.txt")
endif()

string(REPLACE ";" "\n" CMAKE_INSTALL_MANIFEST_CONTENT
       "${CMAKE_INSTALL_MANIFEST_FILES}")
file(WRITE "/root/relic-submission/target-x64-pbc-fam16-766/${CMAKE_INSTALL_MANIFEST}"
     "${CMAKE_INSTALL_MANIFEST_CONTENT}")

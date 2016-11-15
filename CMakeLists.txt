cmake_minimum_required(VERSION 2.8)
project(smartmontools)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -g")

set(CMAKE_EXE_LINKER_FLAGS " -static-libstdc++ ")

add_executable(smarthealth
        smart_health.cpp
        atacmdnames.o
        ataidentify.o
        cciss.o
        dev_ata_cmd_set.o
        knowndrives.o
        nvmeprint.cpp
        scsiata.o
        scsiprint.cpp
        atacmds.o
        ataprint.cpp
        dev_areca.o
        dev_interface.o
        nvmecmds.o
        os_linux.o
        scsicmds.o
        utility.o
        )
# 
# source files 
#

SOURCES = rfw_timer.cpp

#
# parameters for various compilers
#

GCC_NAME    = g++
GCC_FLAGS   = -Wall -O4 -ansi -pedantic -fpermissive
GCC_LIBS    = -lm -L/usr/lib32/
GCC_DEFINES = -DRFW_RUSAGE
GCC_OBJECTS = $(SOURCES:.cpp=.o)

VCC_NAME    = cl 
VCC_FLAGS   = -O2 /W4
VCC_DEFINES = -DWIN32 -DNDEBUG -D_CONSOLE 
VCC_LIBS    = -lm
VCC_OBJECTS = $(SOURCES:.cpp=.obj)

CC_NAME     = CC
CC_FLAGS    = -O3 -OPT:Olimit_opt=on -LANG:std
#CC_FLAGS    = -LANG:std
CC_DEFINES  = -DRFW_RUSAGE
CC_LIBS     = -lm -L/usr/lib32/mips3/
CC_OBJECTS  = $(SOURCES:.cpp=.o)

#
# CHANGE THESE LINES TO USE YOUR FAVORITE COMPILER
CCC      = $(GCC_NAME)
FLAGS    = $(GCC_FLAGS)
LIBS     = $(GCC_LIBS)
DEFINES  = $(GCC_DEFINES)
OBJECTS  = $(GCC_OBJECTS)
INCLUDES = -I.

.SUFFIXES: .cpp


dbs: $(OBJECTS) DSNCA1.o
	$(CCC) $(FLAGS) $(DEFINES) $(INCLUDES) $(OBJECTS) DSNCA1.o $(LIBS) -o DSNCA1


all: clean DSNCA1

clean: 
	'rm' *.o
	
.cpp.o:
	$(CCC) $(DEFINES) $(FLAGS) -c $<

.cpp.obj:
	$(CCC) $(DEFINES) $(FLAGS) -c $<


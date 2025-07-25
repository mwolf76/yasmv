# Makefile for ucodeopt
# High-performance CNF optimizer for yasmv microcode files

CXX = g++
CXXFLAGS = -std=c++17 -O3 -march=native -Wall -Wextra -pthread
LDFLAGS = -ljsoncpp -pthread

# Debug build
DEBUG_FLAGS = -g -O0 -DDEBUG -fsanitize=address,undefined
DEBUG_LDFLAGS = -fsanitize=address,undefined

TARGET = ucodeopt
SOURCE = ucodeopt.cc

.PHONY: all clean debug

all: $(TARGET)

$(TARGET): $(SOURCE)
	$(CXX) $(CXXFLAGS) -o $@ $< $(LDFLAGS)

debug: $(SOURCE)
	$(CXX) $(CXXFLAGS) $(DEBUG_FLAGS) -o $(TARGET)-debug $< $(LDFLAGS) $(DEBUG_LDFLAGS)

clean:
	rm -f $(TARGET) $(TARGET)-debug

# Installation (optional)
PREFIX ?= /usr/local
install: $(TARGET)
	install -m 755 $(TARGET) $(PREFIX)/bin/

uninstall:
	rm -f $(PREFIX)/bin/$(TARGET)

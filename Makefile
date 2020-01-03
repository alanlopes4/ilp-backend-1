
PLUGIN=plugin_alan.so
SOURCES=\
        plugin_alan.cc \
		$(END)

include ../Makefile.common

.PHONY: test
test: $(PLUGIN)
	$(CCPLUGIN) -c -o /dev/null test.c

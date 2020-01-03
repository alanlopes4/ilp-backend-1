PLUGIN=plugin_alan.so
SOURCES=\
        plugin_alan.cc \
		$(END)

include ../Makefile.common

.PHONY: test

test: $(PLUGIN)
	$(CCPLUGIN) -c -o -w -I$(DEP) /dev/null $(PROGRAMA) 




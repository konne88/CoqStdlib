NAME=Library
BUILD=.build

CP=cp
UNAME := $(shell uname -s)
ifeq ($(UNAME),Darwin)
	CP=gcp
endif

build= \
.PHONY: main clean

main:
	mkdir $(BUILD) 2>/dev/null || true
	find . -not -path '*/\.*' -name '*.v' -exec $(CP) -a --parents -t $(BUILD) {} +
	cd $(BUILD); find . -name '*.v' -exec coq_makefile -R . $(NAME) -o Makefile {} +
	make -j `nproc` -C$(BUILD)



#	cd $(BUILD); find . -name '*.v' | xargs coq_makefile -R . $(NAME) -o Makefile; cd -;\
#	make -j4 -C$(BUILD)

clean:
	rm -r $(BUILD)

all: hott

hott: hott.agdai

%.agdai: %.agda
	agda $<

clean:
	find . -type f -iname '*.agdai' -delete

.PHONY: clean

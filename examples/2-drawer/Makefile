
diagman: Drawer.kc
	stack run -- Drawer.kc --output-c && cc "test.c" -I../../kcsrc/vendor -Wunused -L../../ddd/ext/ -lraylib -o diagman

build: diagman

run: build
	./diagman

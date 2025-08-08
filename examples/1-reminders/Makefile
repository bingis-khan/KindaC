
remind: # *.kc
	stack run -- "Main.kc" --output-c && cc "test.c" -Wunused -o "Main.out"
	mv Main.out reminda

run: remind
	./reminda

deploy: reminda
	cp reminda ~/.local/bin/

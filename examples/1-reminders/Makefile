
reminda: Main.kc
	stack run -- "Main.kc" --output-c && cc "test.c" -Wunused -o "reminda"

run: reminda
	./reminda

deploy: reminda
	cp reminda ~/.local/bin/

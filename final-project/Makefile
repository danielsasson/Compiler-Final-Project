all: clean $(MAKECMDGOALS)




$(MAKECMDGOALS).s:
	echo '(load "project/sexpr-parser.scm") (load "project/tag-parser.scm") (load "project/semantic-analyzer.scm") (load "project/compiler.scm") (compile-scheme-file "$(MAKECMDGOALS).scm" "$(MAKECMDGOALS).s")' | scheme -q

$(MAKECMDGOALS).o: $(MAKECMDGOALS).s 
	nasm -f elf64 $(MAKECMDGOALS).s -o $(MAKECMDGOALS).o 

$(MAKECMDGOALS): $(MAKECMDGOALS).o 
	gcc -m64 -Wall -g $(MAKECMDGOALS).o -o $(MAKECMDGOALS)

.PHONY: clean

#Clean the build directory
clean: 
	rm -f *.o $(MAKECMDGOALS)





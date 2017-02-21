all:

update: js ocamldoc

js:
	$(MAKE) -C ../src web
	chmod a+w catt.js
	cp ../src/catt.js .
	chmod a-w catt.js

ocamldoc:
	$(MAKE) -C ../src htdoc
	mkdir -p ocamldoc
	cp ../src/doc/catt/html/* ocamldoc/
	-git add ocamldoc/*.html

ci: update
	git ci . -m "Update website."
	git push

.PHONY: ocamldoc

all:

update: js ocamldoc

js:
	$(MAKE) -C ../src web
	chmod a+w catt.html catt.css catt.js
	cp ../src/catt.html ../src/catt.css ../src/catt.js .
	chmod a-w catt.html catt.css catt.js

ocamldoc:
	$(MAKE) -C ../src htdoc
	mkdir -p ocamldoc
	cp ../src/doc/catt/html/* ocamldoc/
	-git add ocamldoc/*.html

ci: update
	git ci . -m "Update website."
	git push

.PHONY: ocamldoc

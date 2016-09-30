all:

update:
	$(MAKE) -C ../src web
	chmod a+w catt.html catt.css catt.js
	cp ../src/catt.html ../src/catt.css ../src/catt.js .
	chmod a-w catt.html catt.css catt.js

ci: update
	git ci . -m "Update website."

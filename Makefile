generate: 
	~/.local/bin/agda-2.9.0 Everything.agda -i. -isrc --html --html-dir=html -vhtml:0
	cp html/Everything.html html/index.html

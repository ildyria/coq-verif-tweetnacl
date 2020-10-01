tweetverif-supplementary.pdf: previous.pdf tweetverif-USENIX.pdf tweetverif-SP.pdf
	pdftk $^ cat output $@

previous.pdf: previous.tex reviews-usenix.tex tweetverif-USENIX.pdf tweetverif-SP.pdf
	pdflatex previous.tex


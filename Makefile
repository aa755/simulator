all: anim.pdf

simulator: simulator.hs
	ghc simulator.hs -o simulator -main-is Simulator


frames.tex: simulator
	./simulator > frames.tex

framesPaginated.tex : frames.tex
	echo '\\begin{frame}\\begin{tikzpicture}[scale=0.02]' > framesPaginated.tex
	sed 's/newframe\*/end{tikzpicture}\\end{frame}\n\\begin{frame}\\begin{tikzpicture}[scale=0.02]/g' frames.tex | head -n -3 > temp.tex
	sed 's/newframe/end{tikzpicture}\\end{frame}\n\\begin{frame}\\begin{tikzpicture}[scale=0.02]/g' temp.tex >> framesPaginated.tex

anim.pdf: simulator framesPaginated.tex anim.tex
	pdflatex anim.tex


clean:
	rm anim.nav anim.aux anim.out anim.snm anim.toc anim.pdf framesPaginated.tex

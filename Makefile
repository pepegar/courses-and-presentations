source := slides-md
output := slides
sources := $(wildcard $(source)/*.md)
objects := $(patsubst %.md,%.pdf,$(subst $(source),$(output),$(sources)))

all: $(objects)

session5:
	pandoc \
    --template handouts/handout.tex \
    handouts/session5.md \
    -o handouts/session5.pdf

# --filter pandoc-crossref \
# --pdf-engine=xelatex \
# --highlight-style=tango \
# --toc \
# -N \
# --variable monofont="PragmataPro Mono" \
# --variable fontsize=12pt \

$(output)/%.pdf: $(source)/%.md
	pandoc \
		--pdf-engine=xelatex	 \
		--variable monofont="PragmataPro Mono" \
		--variable fontsize=12pt \
		--variable theme=Madrid \
		-f markdown $< \
		-t beamer \
		--highlight-style tango \
		-o $@

.PHONY : clean

watch:
	ls $(source)/*.md | entr make all

hugo:
	hugo --source site server -D

clean:
	rm -f $(output)/*.pdf

from pathlib import Path
root=Path(__file__).resolve().parents[1]
b=root/'blueprint'; src=b/'src'
body=(src/'content.tex').read_text().replace(r'\input{../src/inventory}',(src/'inventory.tex').read_text())
pre=r'''\documentclass[10pt,oneside]{book}
\usepackage[margin=1in]{geometry}
'''+(src/'macros/common.tex').read_text()+'\n'+(src/'macros/print.tex').read_text()+r'''
\usepackage{lmodern,microtype,xurl}
\setlength{\emergencystretch}{4em}
\setlength{\parskip}{.35em}
\setlength{\parindent}{0pt}
\renewcommand{\source}[1]{\par\smallskip\noindent\textit{Manuscript label:} \nolinkurl{#1}.\par}
\title{Oberwolfach formalisation\\Blueprint and partial verification}
\author{Formalisation working document}
\date{20 October 2026}
\begin{document}
\hypersetup{pageanchor=false}
\maketitle
\hypersetup{pageanchor=true}
\tableofcontents
'''
(b/'print/main.tex').write_text('% Generated; edit blueprint/src instead.\n'+pre+body+'\n\\end{document}\n')

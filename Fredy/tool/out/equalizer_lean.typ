#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(width: auto, height: auto, margin: 9mm)
#set text(size: 11pt, font: "New Computer Modern")

#align(center)[#text(13pt, weight: "bold")[An EQUALIZER diagram (§1.428)]]

#align(center)[
#grid(columns: 5, align: horizon, column-gutter: 7mm,
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 2), $E$), node((2, 2), $A$), node((4, 2), $B$), node((3, 2), $div$), edge((0, 2), (2, 2), "->"), edge((2, 2), (4, 2), $x$, "->", shift: 8pt, label-side: left), edge((2, 2), (4, 2), $y$, "->", shift: -8pt, label-side: right)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$forall$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 2), $E$), node((2, 2), $A$), node((4, 2), $B$), node((2, 0), $T$), node((3, 2), $div$), edge((2, 0), (2, 2), $z$, "->"), edge((0, 2), (2, 2), "->"), edge((2, 2), (4, 2), $x$, "->", shift: 8pt, label-side: left), edge((2, 2), (4, 2), $y$, "->", shift: -8pt, label-side: right)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$exists #h(1pt) !$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 2), $E$), node((2, 2), $A$), node((4, 2), $B$), node((2, 0), $T$), node((3, 2), $div$), edge((2, 0), (0, 2), $u$, "->"), edge((2, 0), (2, 2), $z$, "->"), edge((0, 2), (2, 2), "->"), edge((2, 2), (4, 2), $x$, "->", shift: 8pt, label-side: left), edge((2, 2), (4, 2), $y$, "->", shift: -8pt, label-side: right))
)
]

#align(center)[#text(9pt, style: "italic")[∀ z with z x = z y, ∃! u : T→E with u; (E→A) = z]]

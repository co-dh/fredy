#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(width: auto, height: auto, margin: 9mm)
#set text(size: 11pt, font: "New Computer Modern")

#align(center)[#text(13pt, weight: "bold")[A single morphism is monic (§1.41)]]

#align(center)[
#grid(columns: 5, align: horizon, column-gutter: 7mm,
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 1), $A$), node((1, 1), $B$), edge((0, 1), (1, 1), $m$, "->")),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$forall$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 0), $T$), node((0, 1), $A$), node((1, 1), $B$), edge((0, 0), (1, 1), $w$, "->"), edge((0, 1), (1, 1), $m$, "->")),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$!$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 0), $T$), node((0, 1), $A$), node((1, 1), $B$), edge((0, 0), (0, 1), $u$, "->"), edge((0, 0), (1, 1), $w$, "->"), edge((0, 1), (1, 1), $m$, "->"))
)
]

#align(center)[#text(9pt, style: "italic")[∀ w factoring through m, ! (at most one) lift u with u; m = w]]

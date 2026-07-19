#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(width: auto, height: auto, margin: 9mm)
#set text(size: 11pt, font: "New Computer Modern")

#align(center)[#text(13pt, weight: "bold")[A single morphism is monic (§1.41)]]

#align(center)[
#grid(columns: 5, align: horizon, column-gutter: 7mm,
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 2), $A$), node((0, 4), $B$), edge((0, 2), (0, 4), $m$, ">->")),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$forall$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 2), $A$), node((0, 4), $B$), node((0, 0), $T$), edge((0, 2), (0, 4), $m$, ">->"), edge((0, 0), (0, 4), $w$, "->", bend: 22deg)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$!$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 2), $A$), node((0, 4), $B$), node((0, 0), $T$), edge((0, 2), (0, 4), $m$, ">->"), edge((0, 0), (0, 4), $w$, "->", bend: 22deg), edge((0, 0), (0, 2), $u$, "->"))
)
]

#align(center)[#text(9pt, style: "italic")[given m : A → B, ∀ w : T → B, ! (at most one) u : T → A with u m = w]]

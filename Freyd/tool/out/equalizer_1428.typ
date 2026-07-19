#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(width: auto, height: auto, margin: 9mm)
#set text(size: 11pt, font: "New Computer Modern")

#align(center)[#text(13pt, weight: "bold")[The category has equalizers (§1.428)]]

#align(center)[
#grid(columns: 10, align: horizon, column-gutter: 7mm,
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$forall$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 4), $A$), node((0, 6), $B$), edge((0, 4), (0, 6), $f$, "->", shift: 6pt, label-side: left), edge((0, 4), (0, 6), $g$, "->", shift: -6pt, label-side: right)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$exists$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 4), $A$), node((0, 6), $B$), node((0, 2), $E$), edge((0, 4), (0, 6), $f$, "->", shift: 6pt, label-side: left), edge((0, 4), (0, 6), $g$, "->", shift: -6pt, label-side: right), edge((0, 2), (0, 4), $e$, "->")),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$forall$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 4), $A$), node((0, 6), $B$), node((0, 2), $E$), node((0, 0), $Z$), edge((0, 4), (0, 6), $f$, "->", shift: 6pt, label-side: left), edge((0, 4), (0, 6), $g$, "->", shift: -6pt, label-side: right), edge((0, 2), (0, 4), $e$, "->"), edge((0, 0), (0, 4), $z$, "->", bend: 22deg)),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$exists$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 4), $A$), node((0, 6), $B$), node((0, 2), $E$), node((0, 0), $Z$), edge((0, 4), (0, 6), $f$, "->", shift: 6pt, label-side: left), edge((0, 4), (0, 6), $g$, "->", shift: -6pt, label-side: right), edge((0, 2), (0, 4), $e$, "->"), edge((0, 0), (0, 4), $z$, "->", bend: 22deg), edge((0, 0), (0, 2), $m$, "->")),
  box(height: 34mm)[#stack(dir: ttb, spacing: 4mm, align(center)[#text(13pt)[$!$]], line(length: 28mm, angle: 90deg))],
  diagram(spacing: (13mm, 12mm), node-stroke: none, node((0, 4), $A$), node((0, 6), $B$), node((0, 2), $E$), node((0, 0), $Z$), edge((0, 4), (0, 6), $f$, "->", shift: 6pt, label-side: left), edge((0, 4), (0, 6), $g$, "->", shift: -6pt, label-side: right), edge((0, 2), (0, 4), $e$, "->"), edge((0, 0), (0, 4), $z$, "->", bend: 22deg), edge((0, 0), (0, 2), $m$, "->"))
)
]

#align(center)[#text(9pt, style: "italic")[∀ parallel f, g : A→B, ∃ e : E→A (e f = e g) such that ∀ (z : Z→A, z f = z g), ∃ unique m : Z→E with m e = z]]

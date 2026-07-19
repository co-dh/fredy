# Reorg import-path rewrite: Freyd.{A#,L#,Deriv*,rel-cluster} -> AOP./leet./rel.
# Idempotent (new names carry no `Freyd.` prefix), lookahead-safe (never touches
# Freyd.S*, Freyd.Locale, Freyd.WellOrdering, the `Freyd.S2_124` namespace, etc.).
# Applied to tracked *.lean and *.md via: git ls-files '*.lean' '*.md' | xargs perl -pi scripts/reorg_rewrite.pl
s/\bFreyd\.AutoDerive/rel.AutoDerive/g;
s/\bFreyd\.RelInterp/rel.RelInterp/g;
s/\bFreyd\.UnixPipe/rel.UnixPipe/g;
s/\bFreyd\.ShellCommands/rel.ShellCommands/g;
s/\bFreyd\.Deriv1/AOP.Deriv1/g;
s/\bFreyd\.DerivMSS/AOP.DerivMSS/g;
s/\bFreyd\.A(?=[0-9])/AOP.A/g;
s/\bFreyd\.L(?=[0-9])/leet.L/g;
s|\bFreyd/AutoDerive|rel/AutoDerive|g;
s|\bFreyd/RelInterp|rel/RelInterp|g;
s|\bFreyd/UnixPipe|rel/UnixPipe|g;
s|\bFreyd/ShellCommands|rel/ShellCommands|g;
s|\bFreyd/Deriv1|AOP/Deriv1|g;
s|\bFreyd/DerivMSS|AOP/DerivMSS|g;
s|\bFreyd/A(?=[0-9])|AOP/A|g;
s|\bFreyd/L(?=[0-9])|leet/L|g;

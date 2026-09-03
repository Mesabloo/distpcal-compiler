module

import Tests.Linter.Lambda
import Tests.Linter.ExactAbsurd
import Tests.Linter.NoConfusion
import Tests.Linter.RenameI
import Tests.Linter.ByClassical
import Tests.Linter.ByCasesBang
import Tests.Linter.RwShow
import Tests.Linter.RwBeforeSimp
import Tests.Linter.HaveBareName
import Tests.Linter.AdmitScope
import Tests.Linter.AutoImplicitOverride
import Tests.Linter.GoalSelector
import Tests.Linter.FirstSolveSingle
import Tests.Linter.SeqFocusPipe
import Tests.Linter.ByAssumption
import Tests.Linter.ByInArg
import Tests.Linter.AesopTerminal
import Tests.Linter.RwaExact
import Tests.Linter.SimpaUsing
import Tests.Linter.SimpIntro
import Tests.Linter.ObtainRfl
import Tests.Linter.RflHaveSimp
import Tests.Linter.PackUnpack
import Tests.Linter.ByExact
import Tests.Linter.SelectorFirst
import Tests.Linter.SelectorTry
import Tests.Linter.FirstVsSolve
import Tests.Linter.SeqSolveBracket
import Tests.Linter.InductionWith
import Tests.Linter.FirstParens
import Tests.Linter.SetNotLet
import Tests.Linter.ExactBy
import Tests.Linter.SelectorParens
import Tests.Linter.Comments
import Tests.Linter.MvcgenLayout
import Tests.Linter.BlockLayout
import Tests.Linter.SigIndent
import Tests.Linter.RwaExactBare
import Tests.Linter.SelectorOneGoal
import Tests.Linter.UnusedHave
import Tests.Linter.ExistsIntro
import Tests.Linter.BulletSubgoals
import Tests.Linter.UnfoldForeign
import Tests.Linter.HypOrder

/-!
# Style-linter tests

One module per `linter.fugue.*` linter, each a set of `#guard_msgs` blocks. Elaborating these
modules runs the checks; `Tests.Main` imports this so `lake test` covers them.
-/

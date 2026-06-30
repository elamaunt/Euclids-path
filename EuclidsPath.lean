/-
  Корневой модуль консолидации `Euclids-path`.

  Импортирует всю пронумерованную цепочку шагов 00–15.
  Проза-аналог каждого шага лежит в `prose/NN_*.md`.

  Статус формализации (легенда):
    * доказанные шаги    — без `sorry`;
    * открытые места     — помечены `sorry` с комментарием `-- OPEN:`.
  `sorry` подделать нельзя: «зелёный» файл = реально проверенная часть.

  NB: проект ещё не компилировался (Lean не установлен) — см. lakefile.toml.
-/
import EuclidsPath.Step00_Overview
import EuclidsPath.Step01_CenterReduction
import EuclidsPath.Step02_CRTForbiddenClasses
import EuclidsPath.Step03_ActiveSieve
import EuclidsPath.Step04_RankLedger
import EuclidsPath.Step05_DeterminantLaw
import EuclidsPath.Step06_EuclideanPerpetualEngine
import EuclidsPath.Step07_ChargedLedger
import EuclidsPath.Step08_SmallChargedClasses
import EuclidsPath.Step09_CertificateCoverTerminalBridge
import EuclidsPath.Step10_O4CRes
import EuclidsPath.Step11_DASC
import EuclidsPath.Step12_G2
import EuclidsPath.Step13_FinalAssembly
import EuclidsPath.Step14_TwinPrimesInfinity
import EuclidsPath.Step15_OpenProblems
import EuclidsPath.Step16_MultiRankFanCycle
import EuclidsPath.Engine.EPMI
import EuclidsPath.Engine.Carrier
import EuclidsPath.Engine.TwoGap
import EuclidsPath.Engine.Descent

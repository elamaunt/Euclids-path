/-
  Шаг 04 — Ранги слоёв и величина B₅.   Проза: prose/04_RankLedger.md
  Ключ: r±(m) = #{ p∈(A,A²] : p ∣ 6m∓1 };  N_{ij} = #{m : r₋=i, r₊=j};  B₅ = N₀₀ − N₃₃.
        Теор. 6.1: B₅ > 0 ⇒ существует выживший центр ⇒ пара близнецов.
  Статус: 🟢 (переход B₅>0 ⇒ близнецы);  🟡 (что максимальный bad-слой — rank-(3,3)).

  TODO: определить sideRank±, классы N_{ij}, величину B₅ и достаточность.
    def sideRankMinus (A m : ℕ) : ℕ := ((Finset.Icc (A+1) (A*A)).filter (fun p => p.Prime ∧ p ∣ (6*m-1))).card
    theorem B5_pos_imp_twin ... -- → sorry (опирается на Step03 + Bonferroni/ledger Step07)
-/
import EuclidsPath.Step03_ActiveSieve

namespace EuclidsPath

-- (заготовка) определения и леммы шага 04 будут здесь.

end EuclidsPath

# 10. NonCover: survivor ⇒ twin, и мост к бесконечности

> Lean: `Engine/NonCover.lean` (`survivor_of_not_covered`, `infinite_of_unbounded_centers`,
> `prime_of_no_small_prime_factor`, сито-до-корня ⇒ простота).

Если в блоке «плохих» строго меньше, чем carrier, остаётся выживший центр. Сито-до-корня:
old-free + ниже `A²` ⇒ обе стороны простые ⇒ выживший — twin-центр. И если twin-центры неограничены
по `N`, то простых-близнецов бесконечно (`infinite_of_unbounded_centers`). Это мост от блочного
ядра к гипотезе [11].

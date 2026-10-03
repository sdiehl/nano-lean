import Init
namespace NeutralFixture
-- Conversion must not repeatedly normalize the neutral recursive major.
theorem sub_succ (n : Nat) : Nat.succ (n - 2048) = (n - 2048) + 1 := rfl
end NeutralFixture

import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block252

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block252

open Set

def block252W1 : Rat := ((8520774130116217 : Rat) / 10000000000000000)
def block252W2 : Rat := ((8890005979686791 : Rat) / 100000000000000000)
def block252W3 : Rat := ((1639663171409077 : Rat) / 31250000000000000)
def block252W4 : Rat := ((19509969862080323 : Rat) / 100000000000000000)
def block252S1 : Rat := ((18174751 : Rat) / 10000000)
def block252S2 : Rat := ((511587 : Rat) / 200000)
def block252S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block252S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block252V (y : ℝ) : ℝ :=
  ratPotential block252W1 block252W2 block252W3 block252W4 block252S1 block252S2 block252S3 block252S4 y

def block252LeftParamsCertificate : Bool :=
  allBoxesSameParams block252LeftBoxes block252W1 block252W2 block252W3 block252W4 block252S1 block252S2 block252S3 block252S4

theorem block252LeftParamsCertificate_eq_true :
    block252LeftParamsCertificate = true := by
  native_decide

theorem block252_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block252LeftL : ℝ) (block252LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block252S1 : ℝ))
    (hy2ne : y ≠ (block252S2 : ℝ))
    (hy3ne : y ≠ (block252S3 : ℝ))
    (hy4ne : y ≠ (block252S4 : ℝ)) :
    0 < block252V y := by
  have hcert := block252LeftCertificate_eq_true
  unfold block252LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block252LeftBoxes) (lo := block252LeftL) (hi := block252LeftR)
    (w1 := block252W1) (w2 := block252W2) (w3 := block252W3) (w4 := block252W4)
    (s1 := block252S1) (s2 := block252S2) (s3 := block252S3) (s4 := block252S4)
    hboxes hcover block252LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block252RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block252RightChunk000 block252W1 block252W2 block252W3 block252W4 block252S1 block252S2 block252S3 block252S4

theorem block252RightChunk000ParamsCertificate_eq_true :
    block252RightChunk000ParamsCertificate = true := by
  native_decide

theorem block252_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block252RightChunk000L : ℝ) (block252RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block252S1 : ℝ))
    (hy2ne : y ≠ (block252S2 : ℝ))
    (hy3ne : y ≠ (block252S3 : ℝ))
    (hy4ne : y ≠ (block252S4 : ℝ)) :
    0 < block252V y := by
  have hcert := block252RightChunk000Certificate_eq_true
  unfold block252RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block252RightChunk000) (lo := block252RightChunk000L) (hi := block252RightChunk000R)
    (w1 := block252W1) (w2 := block252W2) (w3 := block252W3) (w4 := block252W4)
    (s1 := block252S1) (s2 := block252S2) (s3 := block252S3) (s4 := block252S4)
    hboxes hcover block252RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block252_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block252RightL : ℝ) (block252RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block252S1 : ℝ))
    (hy2ne : y ≠ (block252S2 : ℝ))
    (hy3ne : y ≠ (block252S3 : ℝ))
    (hy4ne : y ≠ (block252S4 : ℝ)) :
    0 < block252V y := by
  have hL : (block252RightChunk000L : ℝ) = (block252RightL : ℝ) := by
    norm_num [block252RightChunk000L, block252RightL]
  have hR : (block252RightChunk000R : ℝ) = (block252RightR : ℝ) := by
    norm_num [block252RightChunk000R, block252RightR]
  have hyc : y ∈ Icc (block252RightChunk000L : ℝ) (block252RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block252_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block252_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block252LeftL : ℝ) (block252LeftR : ℝ) →
    y ≠ 0 → y ≠ (block252S1 : ℝ) → y ≠ (block252S2 : ℝ) →
    y ≠ (block252S3 : ℝ) → y ≠ (block252S4 : ℝ) → 0 < block252V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block252RightL : ℝ) (block252RightR : ℝ) →
    y ≠ 0 → y ≠ (block252S1 : ℝ) → y ≠ (block252S2 : ℝ) →
    y ≠ (block252S3 : ℝ) → y ≠ (block252S4 : ℝ) → 0 < block252V y)

theorem block252_reallog_certificate_proof :
    block252_reallog_certificate := by
  exact ⟨block252_left_V_pos, block252_right_V_pos⟩

end Block252
end M1817475
end Erdos1038Lean

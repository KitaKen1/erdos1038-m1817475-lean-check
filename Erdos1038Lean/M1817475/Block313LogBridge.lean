import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block313

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block313

open Set

def block313W1 : Rat := ((1923403300591581 : Rat) / 2000000000000000)
def block313W2 : Rat := ((3036147022996217 : Rat) / 50000000000000000)
def block313W3 : Rat := ((404941252707981 : Rat) / 1562500000000000)
def block313W4 : Rat := (0 : Rat)
def block313S1 : Rat := ((18174751 : Rat) / 10000000)
def block313S2 : Rat := ((511587 : Rat) / 200000)
def block313S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block313S4 : Rat := ((69973922857142854627 : Rat) / 25000000000000000000)

noncomputable def block313V (y : ℝ) : ℝ :=
  ratPotential block313W1 block313W2 block313W3 block313W4 block313S1 block313S2 block313S3 block313S4 y

def block313LeftParamsCertificate : Bool :=
  allBoxesSameParams block313LeftBoxes block313W1 block313W2 block313W3 block313W4 block313S1 block313S2 block313S3 block313S4

theorem block313LeftParamsCertificate_eq_true :
    block313LeftParamsCertificate = true := by
  native_decide

theorem block313_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block313LeftL : ℝ) (block313LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block313S1 : ℝ))
    (hy2ne : y ≠ (block313S2 : ℝ))
    (hy3ne : y ≠ (block313S3 : ℝ))
    (hy4ne : y ≠ (block313S4 : ℝ)) :
    0 < block313V y := by
  have hcert := block313LeftCertificate_eq_true
  unfold block313LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block313LeftBoxes) (lo := block313LeftL) (hi := block313LeftR)
    (w1 := block313W1) (w2 := block313W2) (w3 := block313W3) (w4 := block313W4)
    (s1 := block313S1) (s2 := block313S2) (s3 := block313S3) (s4 := block313S4)
    hboxes hcover block313LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block313RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block313RightChunk000 block313W1 block313W2 block313W3 block313W4 block313S1 block313S2 block313S3 block313S4

theorem block313RightChunk000ParamsCertificate_eq_true :
    block313RightChunk000ParamsCertificate = true := by
  native_decide

theorem block313_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block313RightChunk000L : ℝ) (block313RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block313S1 : ℝ))
    (hy2ne : y ≠ (block313S2 : ℝ))
    (hy3ne : y ≠ (block313S3 : ℝ))
    (hy4ne : y ≠ (block313S4 : ℝ)) :
    0 < block313V y := by
  have hcert := block313RightChunk000Certificate_eq_true
  unfold block313RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block313RightChunk000) (lo := block313RightChunk000L) (hi := block313RightChunk000R)
    (w1 := block313W1) (w2 := block313W2) (w3 := block313W3) (w4 := block313W4)
    (s1 := block313S1) (s2 := block313S2) (s3 := block313S3) (s4 := block313S4)
    hboxes hcover block313RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block313_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block313RightL : ℝ) (block313RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block313S1 : ℝ))
    (hy2ne : y ≠ (block313S2 : ℝ))
    (hy3ne : y ≠ (block313S3 : ℝ))
    (hy4ne : y ≠ (block313S4 : ℝ)) :
    0 < block313V y := by
  have hL : (block313RightChunk000L : ℝ) = (block313RightL : ℝ) := by
    norm_num [block313RightChunk000L, block313RightL]
  have hR : (block313RightChunk000R : ℝ) = (block313RightR : ℝ) := by
    norm_num [block313RightChunk000R, block313RightR]
  have hyc : y ∈ Icc (block313RightChunk000L : ℝ) (block313RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block313_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block313_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block313LeftL : ℝ) (block313LeftR : ℝ) →
    y ≠ 0 → y ≠ (block313S1 : ℝ) → y ≠ (block313S2 : ℝ) →
    y ≠ (block313S3 : ℝ) → y ≠ (block313S4 : ℝ) → 0 < block313V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block313RightL : ℝ) (block313RightR : ℝ) →
    y ≠ 0 → y ≠ (block313S1 : ℝ) → y ≠ (block313S2 : ℝ) →
    y ≠ (block313S3 : ℝ) → y ≠ (block313S4 : ℝ) → 0 < block313V y)

theorem block313_reallog_certificate_proof :
    block313_reallog_certificate := by
  exact ⟨block313_left_V_pos, block313_right_V_pos⟩

end Block313
end M1817475
end Erdos1038Lean

import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block444

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block444

open Set

def block444W1 : Rat := ((6145690241511637 : Rat) / 10000000000000000)
def block444W2 : Rat := (0 : Rat)
def block444W3 : Rat := ((16263608565897583 : Rat) / 50000000000000000)
def block444W4 : Rat := ((1422745897332199 : Rat) / 20000000000000000)
def block444S1 : Rat := ((18174751 : Rat) / 10000000)
def block444S2 : Rat := ((511587 : Rat) / 200000)
def block444S3 : Rat := ((26290750732142857163 : Rat) / 10000000000000000000)
def block444S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block444V (y : ℝ) : ℝ :=
  ratPotential block444W1 block444W2 block444W3 block444W4 block444S1 block444S2 block444S3 block444S4 y

def block444LeftParamsCertificate : Bool :=
  allBoxesSameParams block444LeftBoxes block444W1 block444W2 block444W3 block444W4 block444S1 block444S2 block444S3 block444S4

theorem block444LeftParamsCertificate_eq_true :
    block444LeftParamsCertificate = true := by
  native_decide

theorem block444_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block444LeftL : ℝ) (block444LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block444S1 : ℝ))
    (hy2ne : y ≠ (block444S2 : ℝ))
    (hy3ne : y ≠ (block444S3 : ℝ))
    (hy4ne : y ≠ (block444S4 : ℝ)) :
    0 < block444V y := by
  have hcert := block444LeftCertificate_eq_true
  unfold block444LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block444LeftBoxes) (lo := block444LeftL) (hi := block444LeftR)
    (w1 := block444W1) (w2 := block444W2) (w3 := block444W3) (w4 := block444W4)
    (s1 := block444S1) (s2 := block444S2) (s3 := block444S3) (s4 := block444S4)
    hboxes hcover block444LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block444RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block444RightChunk000 block444W1 block444W2 block444W3 block444W4 block444S1 block444S2 block444S3 block444S4

theorem block444RightChunk000ParamsCertificate_eq_true :
    block444RightChunk000ParamsCertificate = true := by
  native_decide

theorem block444_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block444RightChunk000L : ℝ) (block444RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block444S1 : ℝ))
    (hy2ne : y ≠ (block444S2 : ℝ))
    (hy3ne : y ≠ (block444S3 : ℝ))
    (hy4ne : y ≠ (block444S4 : ℝ)) :
    0 < block444V y := by
  have hcert := block444RightChunk000Certificate_eq_true
  unfold block444RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block444RightChunk000) (lo := block444RightChunk000L) (hi := block444RightChunk000R)
    (w1 := block444W1) (w2 := block444W2) (w3 := block444W3) (w4 := block444W4)
    (s1 := block444S1) (s2 := block444S2) (s3 := block444S3) (s4 := block444S4)
    hboxes hcover block444RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block444_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block444RightL : ℝ) (block444RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block444S1 : ℝ))
    (hy2ne : y ≠ (block444S2 : ℝ))
    (hy3ne : y ≠ (block444S3 : ℝ))
    (hy4ne : y ≠ (block444S4 : ℝ)) :
    0 < block444V y := by
  have hL : (block444RightChunk000L : ℝ) = (block444RightL : ℝ) := by
    norm_num [block444RightChunk000L, block444RightL]
  have hR : (block444RightChunk000R : ℝ) = (block444RightR : ℝ) := by
    norm_num [block444RightChunk000R, block444RightR]
  have hyc : y ∈ Icc (block444RightChunk000L : ℝ) (block444RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block444_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block444_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block444LeftL : ℝ) (block444LeftR : ℝ) →
    y ≠ 0 → y ≠ (block444S1 : ℝ) → y ≠ (block444S2 : ℝ) →
    y ≠ (block444S3 : ℝ) → y ≠ (block444S4 : ℝ) → 0 < block444V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block444RightL : ℝ) (block444RightR : ℝ) →
    y ≠ 0 → y ≠ (block444S1 : ℝ) → y ≠ (block444S2 : ℝ) →
    y ≠ (block444S3 : ℝ) → y ≠ (block444S4 : ℝ) → 0 < block444V y)

theorem block444_reallog_certificate_proof :
    block444_reallog_certificate := by
  exact ⟨block444_left_V_pos, block444_right_V_pos⟩

end Block444
end M1817475
end Erdos1038Lean

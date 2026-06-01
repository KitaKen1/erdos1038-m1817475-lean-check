import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block120

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block120

open Set

def block120W1 : Rat := ((23249164970414107 : Rat) / 10000000000000000)
def block120W2 : Rat := (0 : Rat)
def block120W3 : Rat := ((9219313886448749 : Rat) / 100000000000000000)
def block120W4 : Rat := ((15857173882903197 : Rat) / 100000000000000000)
def block120S1 : Rat := ((18174751 : Rat) / 10000000)
def block120S2 : Rat := ((511587 : Rat) / 200000)
def block120S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block120S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block120V (y : ℝ) : ℝ :=
  ratPotential block120W1 block120W2 block120W3 block120W4 block120S1 block120S2 block120S3 block120S4 y

def block120LeftParamsCertificate : Bool :=
  allBoxesSameParams block120LeftBoxes block120W1 block120W2 block120W3 block120W4 block120S1 block120S2 block120S3 block120S4

theorem block120LeftParamsCertificate_eq_true :
    block120LeftParamsCertificate = true := by
  native_decide

theorem block120_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block120LeftL : ℝ) (block120LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block120S1 : ℝ))
    (hy2ne : y ≠ (block120S2 : ℝ))
    (hy3ne : y ≠ (block120S3 : ℝ))
    (hy4ne : y ≠ (block120S4 : ℝ)) :
    0 < block120V y := by
  have hcert := block120LeftCertificate_eq_true
  unfold block120LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block120LeftBoxes) (lo := block120LeftL) (hi := block120LeftR)
    (w1 := block120W1) (w2 := block120W2) (w3 := block120W3) (w4 := block120W4)
    (s1 := block120S1) (s2 := block120S2) (s3 := block120S3) (s4 := block120S4)
    hboxes hcover block120LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block120RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block120RightChunk000 block120W1 block120W2 block120W3 block120W4 block120S1 block120S2 block120S3 block120S4

theorem block120RightChunk000ParamsCertificate_eq_true :
    block120RightChunk000ParamsCertificate = true := by
  native_decide

theorem block120_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block120RightChunk000L : ℝ) (block120RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block120S1 : ℝ))
    (hy2ne : y ≠ (block120S2 : ℝ))
    (hy3ne : y ≠ (block120S3 : ℝ))
    (hy4ne : y ≠ (block120S4 : ℝ)) :
    0 < block120V y := by
  have hcert := block120RightChunk000Certificate_eq_true
  unfold block120RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block120RightChunk000) (lo := block120RightChunk000L) (hi := block120RightChunk000R)
    (w1 := block120W1) (w2 := block120W2) (w3 := block120W3) (w4 := block120W4)
    (s1 := block120S1) (s2 := block120S2) (s3 := block120S3) (s4 := block120S4)
    hboxes hcover block120RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block120_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block120RightL : ℝ) (block120RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block120S1 : ℝ))
    (hy2ne : y ≠ (block120S2 : ℝ))
    (hy3ne : y ≠ (block120S3 : ℝ))
    (hy4ne : y ≠ (block120S4 : ℝ)) :
    0 < block120V y := by
  have hL : (block120RightChunk000L : ℝ) = (block120RightL : ℝ) := by
    norm_num [block120RightChunk000L, block120RightL]
  have hR : (block120RightChunk000R : ℝ) = (block120RightR : ℝ) := by
    norm_num [block120RightChunk000R, block120RightR]
  have hyc : y ∈ Icc (block120RightChunk000L : ℝ) (block120RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block120_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block120_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block120LeftL : ℝ) (block120LeftR : ℝ) →
    y ≠ 0 → y ≠ (block120S1 : ℝ) → y ≠ (block120S2 : ℝ) →
    y ≠ (block120S3 : ℝ) → y ≠ (block120S4 : ℝ) → 0 < block120V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block120RightL : ℝ) (block120RightR : ℝ) →
    y ≠ 0 → y ≠ (block120S1 : ℝ) → y ≠ (block120S2 : ℝ) →
    y ≠ (block120S3 : ℝ) → y ≠ (block120S4 : ℝ) → 0 < block120V y)

theorem block120_reallog_certificate_proof :
    block120_reallog_certificate := by
  exact ⟨block120_left_V_pos, block120_right_V_pos⟩

end Block120
end M1817475
end Erdos1038Lean

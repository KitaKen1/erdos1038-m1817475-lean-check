import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block465

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block465

open Set

def block465W1 : Rat := ((5552059150706297 : Rat) / 10000000000000000)
def block465W2 : Rat := (0 : Rat)
def block465W3 : Rat := ((885966890739581 : Rat) / 2500000000000000)
def block465W4 : Rat := ((5559840660490921 : Rat) / 100000000000000000)
def block465S1 : Rat := ((18174751 : Rat) / 10000000)
def block465S2 : Rat := ((511587 : Rat) / 200000)
def block465S3 : Rat := ((131043222410714285833 : Rat) / 50000000000000000000)
def block465S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block465V (y : ℝ) : ℝ :=
  ratPotential block465W1 block465W2 block465W3 block465W4 block465S1 block465S2 block465S3 block465S4 y

def block465LeftParamsCertificate : Bool :=
  allBoxesSameParams block465LeftBoxes block465W1 block465W2 block465W3 block465W4 block465S1 block465S2 block465S3 block465S4

theorem block465LeftParamsCertificate_eq_true :
    block465LeftParamsCertificate = true := by
  native_decide

theorem block465_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block465LeftL : ℝ) (block465LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block465S1 : ℝ))
    (hy2ne : y ≠ (block465S2 : ℝ))
    (hy3ne : y ≠ (block465S3 : ℝ))
    (hy4ne : y ≠ (block465S4 : ℝ)) :
    0 < block465V y := by
  have hcert := block465LeftCertificate_eq_true
  unfold block465LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block465LeftBoxes) (lo := block465LeftL) (hi := block465LeftR)
    (w1 := block465W1) (w2 := block465W2) (w3 := block465W3) (w4 := block465W4)
    (s1 := block465S1) (s2 := block465S2) (s3 := block465S3) (s4 := block465S4)
    hboxes hcover block465LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block465RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block465RightChunk000 block465W1 block465W2 block465W3 block465W4 block465S1 block465S2 block465S3 block465S4

theorem block465RightChunk000ParamsCertificate_eq_true :
    block465RightChunk000ParamsCertificate = true := by
  native_decide

theorem block465_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block465RightChunk000L : ℝ) (block465RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block465S1 : ℝ))
    (hy2ne : y ≠ (block465S2 : ℝ))
    (hy3ne : y ≠ (block465S3 : ℝ))
    (hy4ne : y ≠ (block465S4 : ℝ)) :
    0 < block465V y := by
  have hcert := block465RightChunk000Certificate_eq_true
  unfold block465RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block465RightChunk000) (lo := block465RightChunk000L) (hi := block465RightChunk000R)
    (w1 := block465W1) (w2 := block465W2) (w3 := block465W3) (w4 := block465W4)
    (s1 := block465S1) (s2 := block465S2) (s3 := block465S3) (s4 := block465S4)
    hboxes hcover block465RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block465_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block465RightL : ℝ) (block465RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block465S1 : ℝ))
    (hy2ne : y ≠ (block465S2 : ℝ))
    (hy3ne : y ≠ (block465S3 : ℝ))
    (hy4ne : y ≠ (block465S4 : ℝ)) :
    0 < block465V y := by
  have hL : (block465RightChunk000L : ℝ) = (block465RightL : ℝ) := by
    norm_num [block465RightChunk000L, block465RightL]
  have hR : (block465RightChunk000R : ℝ) = (block465RightR : ℝ) := by
    norm_num [block465RightChunk000R, block465RightR]
  have hyc : y ∈ Icc (block465RightChunk000L : ℝ) (block465RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block465_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block465_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block465LeftL : ℝ) (block465LeftR : ℝ) →
    y ≠ 0 → y ≠ (block465S1 : ℝ) → y ≠ (block465S2 : ℝ) →
    y ≠ (block465S3 : ℝ) → y ≠ (block465S4 : ℝ) → 0 < block465V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block465RightL : ℝ) (block465RightR : ℝ) →
    y ≠ 0 → y ≠ (block465S1 : ℝ) → y ≠ (block465S2 : ℝ) →
    y ≠ (block465S3 : ℝ) → y ≠ (block465S4 : ℝ) → 0 < block465V y)

theorem block465_reallog_certificate_proof :
    block465_reallog_certificate := by
  exact ⟨block465_left_V_pos, block465_right_V_pos⟩

end Block465
end M1817475
end Erdos1038Lean

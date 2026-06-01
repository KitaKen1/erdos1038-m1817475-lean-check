import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block402

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block402

open Set

def block402W1 : Rat := ((1488547809979843 : Rat) / 2000000000000000)
def block402W2 : Rat := (0 : Rat)
def block402W3 : Rat := ((1391699150847997 : Rat) / 5000000000000000)
def block402W4 : Rat := ((9291148498927963 : Rat) / 100000000000000000)
def block402S1 : Rat := ((18174751 : Rat) / 10000000)
def block402S2 : Rat := ((511587 : Rat) / 200000)
def block402S3 : Rat := ((132274816160714285779 : Rat) / 50000000000000000000)
def block402S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block402V (y : ℝ) : ℝ :=
  ratPotential block402W1 block402W2 block402W3 block402W4 block402S1 block402S2 block402S3 block402S4 y

def block402LeftParamsCertificate : Bool :=
  allBoxesSameParams block402LeftBoxes block402W1 block402W2 block402W3 block402W4 block402S1 block402S2 block402S3 block402S4

theorem block402LeftParamsCertificate_eq_true :
    block402LeftParamsCertificate = true := by
  native_decide

theorem block402_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block402LeftL : ℝ) (block402LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block402S1 : ℝ))
    (hy2ne : y ≠ (block402S2 : ℝ))
    (hy3ne : y ≠ (block402S3 : ℝ))
    (hy4ne : y ≠ (block402S4 : ℝ)) :
    0 < block402V y := by
  have hcert := block402LeftCertificate_eq_true
  unfold block402LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block402LeftBoxes) (lo := block402LeftL) (hi := block402LeftR)
    (w1 := block402W1) (w2 := block402W2) (w3 := block402W3) (w4 := block402W4)
    (s1 := block402S1) (s2 := block402S2) (s3 := block402S3) (s4 := block402S4)
    hboxes hcover block402LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block402RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block402RightChunk000 block402W1 block402W2 block402W3 block402W4 block402S1 block402S2 block402S3 block402S4

theorem block402RightChunk000ParamsCertificate_eq_true :
    block402RightChunk000ParamsCertificate = true := by
  native_decide

theorem block402_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block402RightChunk000L : ℝ) (block402RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block402S1 : ℝ))
    (hy2ne : y ≠ (block402S2 : ℝ))
    (hy3ne : y ≠ (block402S3 : ℝ))
    (hy4ne : y ≠ (block402S4 : ℝ)) :
    0 < block402V y := by
  have hcert := block402RightChunk000Certificate_eq_true
  unfold block402RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block402RightChunk000) (lo := block402RightChunk000L) (hi := block402RightChunk000R)
    (w1 := block402W1) (w2 := block402W2) (w3 := block402W3) (w4 := block402W4)
    (s1 := block402S1) (s2 := block402S2) (s3 := block402S3) (s4 := block402S4)
    hboxes hcover block402RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block402RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block402RightChunk001 block402W1 block402W2 block402W3 block402W4 block402S1 block402S2 block402S3 block402S4

theorem block402RightChunk001ParamsCertificate_eq_true :
    block402RightChunk001ParamsCertificate = true := by
  native_decide

theorem block402_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block402RightChunk001L : ℝ) (block402RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block402S1 : ℝ))
    (hy2ne : y ≠ (block402S2 : ℝ))
    (hy3ne : y ≠ (block402S3 : ℝ))
    (hy4ne : y ≠ (block402S4 : ℝ)) :
    0 < block402V y := by
  have hcert := block402RightChunk001Certificate_eq_true
  unfold block402RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block402RightChunk001) (lo := block402RightChunk001L) (hi := block402RightChunk001R)
    (w1 := block402W1) (w2 := block402W2) (w3 := block402W3) (w4 := block402W4)
    (s1 := block402S1) (s2 := block402S2) (s3 := block402S3) (s4 := block402S4)
    hboxes hcover block402RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block402RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block402RightChunk002 block402W1 block402W2 block402W3 block402W4 block402S1 block402S2 block402S3 block402S4

theorem block402RightChunk002ParamsCertificate_eq_true :
    block402RightChunk002ParamsCertificate = true := by
  native_decide

theorem block402_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block402RightChunk002L : ℝ) (block402RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block402S1 : ℝ))
    (hy2ne : y ≠ (block402S2 : ℝ))
    (hy3ne : y ≠ (block402S3 : ℝ))
    (hy4ne : y ≠ (block402S4 : ℝ)) :
    0 < block402V y := by
  have hcert := block402RightChunk002Certificate_eq_true
  unfold block402RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block402RightChunk002) (lo := block402RightChunk002L) (hi := block402RightChunk002R)
    (w1 := block402W1) (w2 := block402W2) (w3 := block402W3) (w4 := block402W4)
    (s1 := block402S1) (s2 := block402S2) (s3 := block402S3) (s4 := block402S4)
    hboxes hcover block402RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block402_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block402RightL : ℝ) (block402RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block402S1 : ℝ))
    (hy2ne : y ≠ (block402S2 : ℝ))
    (hy3ne : y ≠ (block402S3 : ℝ))
    (hy4ne : y ≠ (block402S4 : ℝ)) :
    0 < block402V y := by
  by_cases h0 : y ≤ (block402RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block402RightChunk000L : ℝ) (block402RightChunk000R : ℝ) := by
      have hL : (block402RightChunk000L : ℝ) = (block402RightL : ℝ) := by
        norm_num [block402RightChunk000L, block402RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block402_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block402RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block402RightChunk001L : ℝ) (block402RightChunk001R : ℝ) := by
        have hprev : (block402RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block402RightChunk001L : ℝ) = (block402RightChunk000R : ℝ) := by
          norm_num [block402RightChunk001L, block402RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block402_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block402RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block402RightChunk002L : ℝ) = (block402RightChunk001R : ℝ) := by
        norm_num [block402RightChunk002L, block402RightChunk001R]
      have hR : (block402RightChunk002R : ℝ) = (block402RightR : ℝ) := by
        norm_num [block402RightChunk002R, block402RightR]
      have hyc : y ∈ Icc (block402RightChunk002L : ℝ) (block402RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block402_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block402_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block402LeftL : ℝ) (block402LeftR : ℝ) →
    y ≠ 0 → y ≠ (block402S1 : ℝ) → y ≠ (block402S2 : ℝ) →
    y ≠ (block402S3 : ℝ) → y ≠ (block402S4 : ℝ) → 0 < block402V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block402RightL : ℝ) (block402RightR : ℝ) →
    y ≠ 0 → y ≠ (block402S1 : ℝ) → y ≠ (block402S2 : ℝ) →
    y ≠ (block402S3 : ℝ) → y ≠ (block402S4 : ℝ) → 0 < block402V y)

theorem block402_reallog_certificate_proof :
    block402_reallog_certificate := by
  exact ⟨block402_left_V_pos, block402_right_V_pos⟩

end Block402
end M1817475
end Erdos1038Lean

import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block202

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block202

open Set

def block202W1 : Rat := ((2428350891768771 : Rat) / 2500000000000000)
def block202W2 : Rat := ((2573442726464149 : Rat) / 50000000000000000)
def block202W3 : Rat := ((2216178133086183 : Rat) / 12500000000000000)
def block202W4 : Rat := ((2409121036244773 : Rat) / 25000000000000000)
def block202S1 : Rat := ((18174751 : Rat) / 10000000)
def block202S2 : Rat := ((511587 : Rat) / 200000)
def block202S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block202S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block202V (y : ℝ) : ℝ :=
  ratPotential block202W1 block202W2 block202W3 block202W4 block202S1 block202S2 block202S3 block202S4 y

def block202LeftParamsCertificate : Bool :=
  allBoxesSameParams block202LeftBoxes block202W1 block202W2 block202W3 block202W4 block202S1 block202S2 block202S3 block202S4

theorem block202LeftParamsCertificate_eq_true :
    block202LeftParamsCertificate = true := by
  native_decide

theorem block202_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block202LeftL : ℝ) (block202LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block202S1 : ℝ))
    (hy2ne : y ≠ (block202S2 : ℝ))
    (hy3ne : y ≠ (block202S3 : ℝ))
    (hy4ne : y ≠ (block202S4 : ℝ)) :
    0 < block202V y := by
  have hcert := block202LeftCertificate_eq_true
  unfold block202LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block202LeftBoxes) (lo := block202LeftL) (hi := block202LeftR)
    (w1 := block202W1) (w2 := block202W2) (w3 := block202W3) (w4 := block202W4)
    (s1 := block202S1) (s2 := block202S2) (s3 := block202S3) (s4 := block202S4)
    hboxes hcover block202LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block202RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block202RightChunk000 block202W1 block202W2 block202W3 block202W4 block202S1 block202S2 block202S3 block202S4

theorem block202RightChunk000ParamsCertificate_eq_true :
    block202RightChunk000ParamsCertificate = true := by
  native_decide

theorem block202_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block202RightChunk000L : ℝ) (block202RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block202S1 : ℝ))
    (hy2ne : y ≠ (block202S2 : ℝ))
    (hy3ne : y ≠ (block202S3 : ℝ))
    (hy4ne : y ≠ (block202S4 : ℝ)) :
    0 < block202V y := by
  have hcert := block202RightChunk000Certificate_eq_true
  unfold block202RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block202RightChunk000) (lo := block202RightChunk000L) (hi := block202RightChunk000R)
    (w1 := block202W1) (w2 := block202W2) (w3 := block202W3) (w4 := block202W4)
    (s1 := block202S1) (s2 := block202S2) (s3 := block202S3) (s4 := block202S4)
    hboxes hcover block202RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block202RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block202RightChunk001 block202W1 block202W2 block202W3 block202W4 block202S1 block202S2 block202S3 block202S4

theorem block202RightChunk001ParamsCertificate_eq_true :
    block202RightChunk001ParamsCertificate = true := by
  native_decide

theorem block202_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block202RightChunk001L : ℝ) (block202RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block202S1 : ℝ))
    (hy2ne : y ≠ (block202S2 : ℝ))
    (hy3ne : y ≠ (block202S3 : ℝ))
    (hy4ne : y ≠ (block202S4 : ℝ)) :
    0 < block202V y := by
  have hcert := block202RightChunk001Certificate_eq_true
  unfold block202RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block202RightChunk001) (lo := block202RightChunk001L) (hi := block202RightChunk001R)
    (w1 := block202W1) (w2 := block202W2) (w3 := block202W3) (w4 := block202W4)
    (s1 := block202S1) (s2 := block202S2) (s3 := block202S3) (s4 := block202S4)
    hboxes hcover block202RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block202RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block202RightChunk002 block202W1 block202W2 block202W3 block202W4 block202S1 block202S2 block202S3 block202S4

theorem block202RightChunk002ParamsCertificate_eq_true :
    block202RightChunk002ParamsCertificate = true := by
  native_decide

theorem block202_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block202RightChunk002L : ℝ) (block202RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block202S1 : ℝ))
    (hy2ne : y ≠ (block202S2 : ℝ))
    (hy3ne : y ≠ (block202S3 : ℝ))
    (hy4ne : y ≠ (block202S4 : ℝ)) :
    0 < block202V y := by
  have hcert := block202RightChunk002Certificate_eq_true
  unfold block202RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block202RightChunk002) (lo := block202RightChunk002L) (hi := block202RightChunk002R)
    (w1 := block202W1) (w2 := block202W2) (w3 := block202W3) (w4 := block202W4)
    (s1 := block202S1) (s2 := block202S2) (s3 := block202S3) (s4 := block202S4)
    hboxes hcover block202RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block202RightChunk003ParamsCertificate : Bool :=
  allBoxesSameParams block202RightChunk003 block202W1 block202W2 block202W3 block202W4 block202S1 block202S2 block202S3 block202S4

theorem block202RightChunk003ParamsCertificate_eq_true :
    block202RightChunk003ParamsCertificate = true := by
  native_decide

theorem block202_right_chunk003_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block202RightChunk003L : ℝ) (block202RightChunk003R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block202S1 : ℝ))
    (hy2ne : y ≠ (block202S2 : ℝ))
    (hy3ne : y ≠ (block202S3 : ℝ))
    (hy4ne : y ≠ (block202S4 : ℝ)) :
    0 < block202V y := by
  have hcert := block202RightChunk003Certificate_eq_true
  unfold block202RightChunk003Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block202RightChunk003) (lo := block202RightChunk003L) (hi := block202RightChunk003R)
    (w1 := block202W1) (w2 := block202W2) (w3 := block202W3) (w4 := block202W4)
    (s1 := block202S1) (s2 := block202S2) (s3 := block202S3) (s4 := block202S4)
    hboxes hcover block202RightChunk003ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block202RightChunk004ParamsCertificate : Bool :=
  allBoxesSameParams block202RightChunk004 block202W1 block202W2 block202W3 block202W4 block202S1 block202S2 block202S3 block202S4

theorem block202RightChunk004ParamsCertificate_eq_true :
    block202RightChunk004ParamsCertificate = true := by
  native_decide

theorem block202_right_chunk004_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block202RightChunk004L : ℝ) (block202RightChunk004R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block202S1 : ℝ))
    (hy2ne : y ≠ (block202S2 : ℝ))
    (hy3ne : y ≠ (block202S3 : ℝ))
    (hy4ne : y ≠ (block202S4 : ℝ)) :
    0 < block202V y := by
  have hcert := block202RightChunk004Certificate_eq_true
  unfold block202RightChunk004Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block202RightChunk004) (lo := block202RightChunk004L) (hi := block202RightChunk004R)
    (w1 := block202W1) (w2 := block202W2) (w3 := block202W3) (w4 := block202W4)
    (s1 := block202S1) (s2 := block202S2) (s3 := block202S3) (s4 := block202S4)
    hboxes hcover block202RightChunk004ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block202RightChunk005ParamsCertificate : Bool :=
  allBoxesSameParams block202RightChunk005 block202W1 block202W2 block202W3 block202W4 block202S1 block202S2 block202S3 block202S4

theorem block202RightChunk005ParamsCertificate_eq_true :
    block202RightChunk005ParamsCertificate = true := by
  native_decide

theorem block202_right_chunk005_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block202RightChunk005L : ℝ) (block202RightChunk005R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block202S1 : ℝ))
    (hy2ne : y ≠ (block202S2 : ℝ))
    (hy3ne : y ≠ (block202S3 : ℝ))
    (hy4ne : y ≠ (block202S4 : ℝ)) :
    0 < block202V y := by
  have hcert := block202RightChunk005Certificate_eq_true
  unfold block202RightChunk005Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block202RightChunk005) (lo := block202RightChunk005L) (hi := block202RightChunk005R)
    (w1 := block202W1) (w2 := block202W2) (w3 := block202W3) (w4 := block202W4)
    (s1 := block202S1) (s2 := block202S2) (s3 := block202S3) (s4 := block202S4)
    hboxes hcover block202RightChunk005ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block202_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block202RightL : ℝ) (block202RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block202S1 : ℝ))
    (hy2ne : y ≠ (block202S2 : ℝ))
    (hy3ne : y ≠ (block202S3 : ℝ))
    (hy4ne : y ≠ (block202S4 : ℝ)) :
    0 < block202V y := by
  by_cases h0 : y ≤ (block202RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block202RightChunk000L : ℝ) (block202RightChunk000R : ℝ) := by
      have hL : (block202RightChunk000L : ℝ) = (block202RightL : ℝ) := by
        norm_num [block202RightChunk000L, block202RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block202_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block202RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block202RightChunk001L : ℝ) (block202RightChunk001R : ℝ) := by
        have hprev : (block202RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block202RightChunk001L : ℝ) = (block202RightChunk000R : ℝ) := by
          norm_num [block202RightChunk001L, block202RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block202_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      by_cases h2 : y ≤ (block202RightChunk002R : ℝ)
      · have hyc : y ∈ Icc (block202RightChunk002L : ℝ) (block202RightChunk002R : ℝ) := by
          have hprev : (block202RightChunk001R : ℝ) < y := lt_of_not_ge h1
          have hL : (block202RightChunk002L : ℝ) = (block202RightChunk001R : ℝ) := by
            norm_num [block202RightChunk002L, block202RightChunk001R]
          constructor
          · linarith [hprev, hL]
          · exact h2
        exact block202_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
      ·
        by_cases h3 : y ≤ (block202RightChunk003R : ℝ)
        · have hyc : y ∈ Icc (block202RightChunk003L : ℝ) (block202RightChunk003R : ℝ) := by
            have hprev : (block202RightChunk002R : ℝ) < y := lt_of_not_ge h2
            have hL : (block202RightChunk003L : ℝ) = (block202RightChunk002R : ℝ) := by
              norm_num [block202RightChunk003L, block202RightChunk002R]
            constructor
            · linarith [hprev, hL]
            · exact h3
          exact block202_right_chunk003_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
        ·
          by_cases h4 : y ≤ (block202RightChunk004R : ℝ)
          · have hyc : y ∈ Icc (block202RightChunk004L : ℝ) (block202RightChunk004R : ℝ) := by
              have hprev : (block202RightChunk003R : ℝ) < y := lt_of_not_ge h3
              have hL : (block202RightChunk004L : ℝ) = (block202RightChunk003R : ℝ) := by
                norm_num [block202RightChunk004L, block202RightChunk003R]
              constructor
              · linarith [hprev, hL]
              · exact h4
            exact block202_right_chunk004_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
          ·
            have hprev : (block202RightChunk004R : ℝ) < y := lt_of_not_ge h4
            have hL : (block202RightChunk005L : ℝ) = (block202RightChunk004R : ℝ) := by
              norm_num [block202RightChunk005L, block202RightChunk004R]
            have hR : (block202RightChunk005R : ℝ) = (block202RightR : ℝ) := by
              norm_num [block202RightChunk005R, block202RightR]
            have hyc : y ∈ Icc (block202RightChunk005L : ℝ) (block202RightChunk005R : ℝ) := by
              constructor
              · linarith [hprev, hL]
              · linarith [hy.2, hR]
            exact block202_right_chunk005_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block202_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block202LeftL : ℝ) (block202LeftR : ℝ) →
    y ≠ 0 → y ≠ (block202S1 : ℝ) → y ≠ (block202S2 : ℝ) →
    y ≠ (block202S3 : ℝ) → y ≠ (block202S4 : ℝ) → 0 < block202V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block202RightL : ℝ) (block202RightR : ℝ) →
    y ≠ 0 → y ≠ (block202S1 : ℝ) → y ≠ (block202S2 : ℝ) →
    y ≠ (block202S3 : ℝ) → y ≠ (block202S4 : ℝ) → 0 < block202V y)

theorem block202_reallog_certificate_proof :
    block202_reallog_certificate := by
  exact ⟨block202_left_V_pos, block202_right_V_pos⟩

end Block202
end M1817475
end Erdos1038Lean

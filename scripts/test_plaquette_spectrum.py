"""Small exact fixtures for the connected estimators and their run receipts."""
import contextlib
import io
import math
import struct
import tempfile
import unittest
from pathlib import Path

from analyze_plaquette_spectrum import ANCHOR, estimate, jk_error, read_chain, summary


def bits(x):
    return int.from_bytes(struct.pack(">d", x), "big")


class PlaquetteSpectrumTest(unittest.TestCase):
    def test_periodic_slab_products(self):
        # On the two slabs, interior conditional means and ordinary values differ.
        # Source t=0,4 is frozen. Conditional variance at each interior is 1/64.
        ordinary = [i/16 for i in range(8)]
        sub = [0, 3/16, 2/16, 1/16, 4/16, 7/16, 6/16, 5/16]
        second = [x*x + (1/64 if t % 4 else 0) for t,x in enumerate(sub)]
        lines = ["SLAB4 8 10 1 1 2"]
        for t in range(8):
            lines.append(f"8 10 0 {t} {bits(ordinary[t])} {bits(sub[t])} {bits(second[t])}")
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "chain.tsv"
            p.write_text("\n".join([*lines, "END", ""]))
            metadata, (row,) = read_chain(p)
            self.assertEqual(metadata, (8,10,1,1,2,4))
            x = [v-ANCHOR for v in ordinary]
            y = [v-ANCHOR for v in sub]
            self.assertAlmostEqual(row[2], sum(x[t]*x[(t+1)%8] for t in range(8))/8)
            self.assertAlmostEqual(row[6], sum(y[t]**2+1/64 for t in (1,2,3,5,6,7))/6)
            self.assertAlmostEqual(row[7], (y[0]*y[1]+y[3]*y[4]+y[4]*y[5]+y[7]*y[0])/4)
            self.assertAlmostEqual(row[8], (y[3]*y[5]+y[7]*y[1])/2)
            self.assertAlmostEqual(row[10], (y[1]*y[5]+y[2]*y[6]+y[3]*y[7])/3)
            # With the same ensemble one-point subtraction the offset cancels
            # for direct products. For a selected pair it couples to the sum
            # of its two marginal means, which can differ in a finite sample.
            phases = []
            _, (shifted,) = read_chain(p, 0.625, phases)
            base = estimate([row]*3)
            other = estimate([shifted]*3, 0.625)
            for lag in range(5):
                self.assertAlmostEqual(base[1+lag], other[1+lag])
            endpoint_mean = (sub[3]+sub[5]+sub[7]+sub[1])/2
            self.assertAlmostEqual(other[8]-base[8],
                                   (0.625-ANCHOR)*(2*sum(ordinary)/8-endpoint_mean))
            self.assertEqual(phases, [[0, 0.125, 0, -0.125]])
            p.write_text("\n".join(lines))
            with self.assertRaisesRegex(ValueError, "incomplete"):
                read_chain(p)
            corrupt = lines.copy()
            corrupt[1] = f"8 10 0 0 0 {bits(0.25)} {bits(0.0625)}"
            p.write_text("\n".join([*corrupt, "END", ""]))
            with self.assertRaisesRegex(ValueError, "frozen"):
                read_chain(p)

    def test_periodic_single_energy_including_midpoint(self):
        # P swaps the states. Its one-point function vanishes and spectrum is (1,1/2).
        q = 0.5
        corr = [(q**d + q**(8-d))/(1+q**8) for d in range(5)]
        chains = [[0, *corr, *corr] for _ in range(4)]
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            summary(chains, 8)
        energy_rows = [line.split() for line in out.getvalue().splitlines() if line.startswith("8\tdirect\t")]
        self.assertEqual([int(row[2]) for row in energy_rows], [1,2,3,4])
        for row in energy_rows:
            self.assertAlmostEqual(float(row[3]), math.log(2), places=7)
        self.assertEqual(energy_rows[-1][-1], "within_tolerance")

    def test_centering_and_chain_uncertainty(self):
        x = [0, 1/4, 1/2, 3/4]
        result = estimate([[v, v*v] for v in x])
        pair_mean = (0.25*0.5 + 0.25*0.75 + 0.5*0.75)/6
        self.assertAlmostEqual(result[1], sum(v*v for v in x)/4 - pair_mean)
        # Leave-one-out averages of four independent chain-level observations.
        deletes = [(sum(x)-v)/3 for v in x]
        self.assertAlmostEqual(jk_error(deletes), math.sqrt(5/192))


if __name__ == "__main__":
    unittest.main()

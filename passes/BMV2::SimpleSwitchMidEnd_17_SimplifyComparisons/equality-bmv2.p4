*** dumps/p4_16_samples/equality-bmv2.p4/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 16:58:16.165271400 +0200
--- dumps/p4_16_samples/equality-bmv2.p4/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:58:16.168311000 +0200
*************** control ingress(inout headers hdr, inout
*** 32,42 ****
              hdr.same.same = hdr.same.same | 8w1;
          if (hdr.h.v == hdr.a[0].v) 
              hdr.same.same = hdr.same.same | 8w2;
!         if (hdr.h == hdr.a[0]) 
              hdr.same.same = hdr.same.same | 8w4;
          tmp[0] = hdr.h;
          tmp[1] = hdr.a[0];
!         if (tmp == hdr.a) 
              hdr.same.same = hdr.same.same | 8w8;
      }
  }
--- 32,42 ----
              hdr.same.same = hdr.same.same | 8w1;
          if (hdr.h.v == hdr.a[0].v) 
              hdr.same.same = hdr.same.same | 8w2;
!         if (!hdr.h.isValid() && !hdr.a[0].isValid() || hdr.h.isValid() && hdr.a[0].isValid() && hdr.h.s == hdr.a[0].s && hdr.h.v == hdr.a[0].v) 
              hdr.same.same = hdr.same.same | 8w4;
          tmp[0] = hdr.h;
          tmp[1] = hdr.a[0];
!         if (true && (!tmp[0].isValid() && !hdr.a[0].isValid() || tmp[0].isValid() && hdr.a[0].isValid() && tmp[0].s == hdr.a[0].s && tmp[0].v == hdr.a[0].v) && (!tmp[1].isValid() && !hdr.a[1].isValid() || tmp[1].isValid() && hdr.a[1].isValid() && tmp[1].s == hdr.a[1].s && tmp[1].v == hdr.a[1].v)) 
              hdr.same.same = hdr.same.same | 8w8;
      }
  }

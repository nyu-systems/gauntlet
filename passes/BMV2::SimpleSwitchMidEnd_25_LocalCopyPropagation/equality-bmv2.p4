*** dumps/p4_16_samples/equality-bmv2.p4/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:16.188970600 +0200
--- dumps/p4_16_samples/equality-bmv2.p4/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:16.191742200 +0200
*************** control ingress(inout headers hdr, inout
*** 29,35 ****
          hdr.same.same = 8w0;
          stdmeta.egress_spec = 9w0;
          if (hdr.h.s == hdr.a[0].s) 
!             hdr.same.same = hdr.same.same | 8w1;
          if (hdr.h.v == hdr.a[0].v) 
              hdr.same.same = hdr.same.same | 8w2;
          if (!hdr.h.isValid() && !hdr.a[0].isValid() || hdr.h.isValid() && hdr.a[0].isValid() && hdr.h.s == hdr.a[0].s && hdr.h.v == hdr.a[0].v) 
--- 29,35 ----
          hdr.same.same = 8w0;
          stdmeta.egress_spec = 9w0;
          if (hdr.h.s == hdr.a[0].s) 
!             hdr.same.same = 8w0 | 8w1;
          if (hdr.h.v == hdr.a[0].v) 
              hdr.same.same = hdr.same.same | 8w2;
          if (!hdr.h.isValid() && !hdr.a[0].isValid() || hdr.h.isValid() && hdr.a[0].isValid() && hdr.h.s == hdr.a[0].s && hdr.h.v == hdr.a[0].v) 

*** dumps/p4_16_samples/subparser-with-header-stack-bmv2.p4/pruned/subparser-with-header-stack-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:00:37.349760400 +0200
--- dumps/p4_16_samples/subparser-with-header-stack-bmv2.p4/pruned/subparser-with-header-stack-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:00:37.221238500 +0200
*************** parser parserI(packet_in pkt, out header
*** 42,52 ****
          }
      }
      state parse_first_h2 {
!         hdr_1 = hdr;
          pkt.extract<h2_t>(hdr_1.h2.next);
          verify(hdr_1.h2.last.hdr_type == 8w2, error.BadHeaderType);
          ret_next_hdr_type = hdr_1.h2.last.next_hdr_type;
!         hdr = hdr_1;
          my_next_hdr_type = ret_next_hdr_type;
          transition select(my_next_hdr_type) {
              8w2: parse_other_h2;
--- 42,60 ----
          }
      }
      state parse_first_h2 {
!         {
!             hdr_1.h1 = hdr.h1;
!             hdr_1.h2 = hdr.h2;
!             hdr_1.h3 = hdr.h3;
!         }
          pkt.extract<h2_t>(hdr_1.h2.next);
          verify(hdr_1.h2.last.hdr_type == 8w2, error.BadHeaderType);
          ret_next_hdr_type = hdr_1.h2.last.next_hdr_type;
!         {
!             hdr.h1 = hdr_1.h1;
!             hdr.h2 = hdr_1.h2;
!             hdr.h3 = hdr_1.h3;
!         }
          my_next_hdr_type = ret_next_hdr_type;
          transition select(my_next_hdr_type) {
              8w2: parse_other_h2;

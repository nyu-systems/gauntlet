--- dumps/p4_16_samples/subparser-with-header-stack-bmv2.p4/pruned/subparser-with-header-stack-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:32:18.251409400 +0200
+++ dumps/p4_16_samples/subparser-with-header-stack-bmv2.p4/pruned/subparser-with-header-stack-bmv2-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 17:32:18.254459600 +0200
@@ -43,15 +43,9 @@ parser parserI(packet_in pkt, out header
     }
     state parse_first_h2 {
         hdr_1 = hdr;
-        transition subParserImpl_start;
-    }
-    state subParserImpl_start {
         pkt.extract<h2_t>(hdr_1.h2.next);
         verify(hdr_1.h2.last.hdr_type == 8w2, error.BadHeaderType);
         ret_next_hdr_type = hdr_1.h2.last.next_hdr_type;
-        transition parse_first_h2_0;
-    }
-    state parse_first_h2_0 {
         hdr = hdr_1;
         my_next_hdr_type = ret_next_hdr_type;
         transition select(my_next_hdr_type) {

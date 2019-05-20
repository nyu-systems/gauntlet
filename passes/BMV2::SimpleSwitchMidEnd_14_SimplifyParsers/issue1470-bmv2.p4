--- dumps/p4_16_samples/issue1470-bmv2.p4/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:30:17.361561000 +0200
+++ dumps/p4_16_samples/issue1470-bmv2.p4/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-05-20 17:30:17.364422000 +0200
@@ -30,9 +30,6 @@ parser OuterParser(packet_in pkt, out he
     state start {
         hdr_1.eth.setInvalid();
         hdr_1.ipv4.setInvalid();
-        transition InnerParser_start;
-    }
-    state InnerParser_start {
         pkt.extract<eth_h>(hdr_1.eth);
         transition select(hdr_1.eth.type) {
             16w0x800: InnerParser_parse_ipv4;

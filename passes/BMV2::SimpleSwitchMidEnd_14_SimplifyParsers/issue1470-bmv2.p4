--- dumps/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:32:02.597345300 +0200
+++ dumps/pruned/issue1470-bmv2-BMV2::SimpleSwitchMidEnd_14_SimplifyParsers.p4	2019-06-08 18:32:02.599748400 +0200
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

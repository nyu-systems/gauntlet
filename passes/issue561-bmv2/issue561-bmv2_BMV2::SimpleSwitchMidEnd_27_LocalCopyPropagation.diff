--- before_pass
+++ after_pass
@@ -89,9 +89,7 @@ struct Tcp_option_sack_top {
 }
 parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
     bit<7> Tcp_option_parser_tcp_hdr_bytes_left;
-    bit<8> Tcp_option_parser_n_sack_bytes;
     bit<8> Tcp_option_parser_tmp;
-    Tcp_option_sack_top Tcp_option_parser_tmp_0;
     bit<16> tmp;
     state start {
         packet.extract<ethernet_t>(hdr.ethernet);
@@ -206,16 +204,11 @@ parser ParserImpl(packet_in packet, out
     state Tcp_option_parser_parse_tcp_option_sack {
         {
             tmp = packet.lookahead<bit<16>>();
-            {
-                Tcp_option_parser_tmp_0.kind = tmp[15:8];
-                Tcp_option_parser_tmp_0.length = tmp[7:0];
-            }
         }
-        Tcp_option_parser_n_sack_bytes = Tcp_option_parser_tmp_0.length;
-        verify(Tcp_option_parser_n_sack_bytes == 8w10 || Tcp_option_parser_n_sack_bytes == 8w18 || Tcp_option_parser_n_sack_bytes == 8w26 || Tcp_option_parser_n_sack_bytes == 8w34, error.TcpBadSackOptionLength);
-        verify(Tcp_option_parser_tcp_hdr_bytes_left >= (bit<7>)Tcp_option_parser_n_sack_bytes, error.TcpOptionTooLongForHeader);
-        Tcp_option_parser_tcp_hdr_bytes_left = Tcp_option_parser_tcp_hdr_bytes_left - (bit<7>)Tcp_option_parser_n_sack_bytes;
-        packet.extract<Tcp_option_sack_h>(hdr.tcp_options_vec.next.sack, (bit<32>)((Tcp_option_parser_n_sack_bytes << 3) + 8w240));
+        verify(tmp[7:0] == 8w10 || tmp[7:0] == 8w18 || tmp[7:0] == 8w26 || tmp[7:0] == 8w34, error.TcpBadSackOptionLength);
+        verify(Tcp_option_parser_tcp_hdr_bytes_left >= (bit<7>)tmp[7:0], error.TcpOptionTooLongForHeader);
+        Tcp_option_parser_tcp_hdr_bytes_left = Tcp_option_parser_tcp_hdr_bytes_left - (bit<7>)tmp[7:0];
+        packet.extract<Tcp_option_sack_h>(hdr.tcp_options_vec.next.sack, (bit<32>)((tmp[7:0] << 3) + 8w240));
         transition Tcp_option_parser_next_option;
     }
     state parse_tcp_0 {

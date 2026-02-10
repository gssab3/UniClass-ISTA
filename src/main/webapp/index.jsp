<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.uniclass.utenti.model.Utente" %>

<%
	Utente u = (Utente) session.getAttribute("currentSessionUser");
%>

<!DOCTYPE html>
<html lang="it">
<head>
	<meta charset="UTF-8">
	<title>Home</title>
</head>
<body>

<h1>Benvenuto nella Home!</h1>

<p>
	Utente loggato:
	<strong><%= (u != null ? u.getEmail() : "Nessuno") %></strong>
</p>

</body>
</html>

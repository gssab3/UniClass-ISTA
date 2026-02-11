<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.uniclass.utenti.model.Utente, it.unisa.uniclass.utenti.model.Tipo" %>
<%@ page import="it.unisa.uniclass.orari.model.CorsoLaurea" %>
<%@ page import="java.util.List" %>

<%
	/* Sessione HTTP */
	HttpSession sessione = request.getSession(false);
	Utente user = null;

	if (sessione != null) {
		user = (Utente) sessione.getAttribute("currentSessionUser");
		if (user != null) {
			sessione.setAttribute("utenteEmail", user.getEmail());
		} else {
			sessione.removeAttribute("utenteEmail");
		}
	}

	/* Controllo tipo utente */
	Tipo tipoUtente = null;
	if(user != null) {
		tipoUtente = (Tipo) user.getTipo();
	}

	List<CorsoLaurea> corsiLaurea = (List<CorsoLaurea>) request.getAttribute("corsi");
%>

<!DOCTYPE html>
<html lang="it" xml:lang="it">
<head>
	<title>UniClass</title>
	<script src="scripts/sidebar.js" type="text/javascript"></script>
	<link type="text/css" rel="stylesheet" href="styles/headerStyle.css"/>
	<link type="text/css" rel="stylesheet" href="styles/barraNavigazioneStyle.css"/>
	<link type="text/css" rel="stylesheet" href="styles/formcss.css"/>
	<link type="text/css" rel="stylesheet" href="styles/footerstyle.css">
	<link rel="icon" href="images/logois.png" sizes="32x32" type="image/png">
</head>

<body>

<div class="barraNavigazione" id="barraNavigazione">
	<a href="javascript:void(0)" class="closebtn" onclick="closeNav()">
		<img src="images/icons/menuOpenIcon.png" alt="closebtn">
	</a>
	<p>Menu</p>
	<ul id="menu">
		<li id="aule"><a href="AulaServlet">Aule</a></li>
		<li id="mappa"><a href="mappa.jsp">Mappa</a></li>
		<li id="ChatBot"><a href="ChatBot.jsp">ChatBot</a></li>
		<li id="infoapp"><a href="infoapp.jsp">Info App</a></li>
		<li id="aboutus"><a href="aboutus.jsp">Chi Siamo</a></li>
	</ul>
</div>

<jsp:include page="header.jsp"/>

<br> <br>

<div id="contieniForm">
	<form id="cercaOrarioForm" action="cercaOrario" method="POST">
		<label for="corsoLaurea">Corso di Laurea:</label>
		<select id="corsoLaurea" name="corsoLaurea" onchange="aggiornaResto()" required>
			<option value="">-- Seleziona un corso --</option>
			<%
				if (corsiLaurea != null) {
					for (CorsoLaurea cors : corsiLaurea) {
						String corso = cors.getNome();
			%>
			<option value="<%= corso %>"><%= corso %></option>
			<%
					}
				}
			%>
		</select>

		<label for="resto">Resto:</label>
		<select id="resto" name="resto" required>
			<option value="">-- Seleziona un resto --</option>
		</select>

		<label for="anno">Anno:</label>
		<select id="anno" name="anno" required>
			<option value="">-- Seleziona un anno --</option>
		</select>

		<button type="submit">Cerca Orario</button>
	</form>
</div>

<script>
	// Definisco contextPath PRIMA di caricare il file JS esterno
	const contextPath = "<%= request.getContextPath() %>";
</script>

<script src="scripts/formOrario.js"></script>

<script>
	document.getElementById("cercaOrarioForm").addEventListener("submit", function(event) {
		const corsoLaurea = document.getElementById("corsoLaurea").value;
		const resto = document.getElementById("resto").value;
		const anno = document.getElementById("anno").value;
		console.log("Submit -> Corso:", corsoLaurea, " Resto:", resto, " Anno:", anno);
	});
</script>

<br>
<%@include file = "footer.jsp" %>
</body>
</html>
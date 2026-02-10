<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.uniclass.utenti.model.Utente" %>
<%@ page import="it.unisa.uniclass.utenti.model.Accademico" %>
<%@ page import="it.unisa.uniclass.utenti.model.Ruolo" %>

<%
    // Recupero Utente dalla Sessione
    Utente u = (Utente) session.getAttribute("currentSessionUser");

    // Redirect se non loggato
    if (u == null) {
        response.sendRedirect("Login.jsp");
        return;
    }

    // Preparazione dati per la visualizzazione
    boolean isAccademico = (u instanceof Accademico);
    Accademico acc = isAccademico ? (Accademico) u : null;

    String userIcon = "images/icons/usericonlog.png"; // Default
    String ruoloStr = "Utente";

    if (isAccademico && acc != null) {
        if (acc.getRuolo() == Ruolo.Studente) {
            userIcon = "images/icons/iconstudent.png";
            ruoloStr = "Studente";
        } else if (acc.getRuolo() == Ruolo.DOCENTE) {
            userIcon = "images/icons/iconprof.png";
            ruoloStr = "Docente";
        } else if (acc.getRuolo() == Ruolo.COORDINATORE) {
            userIcon = "images/icons/iconprof.png";
            ruoloStr = "Coordinatore";
        }
    } else {
        userIcon = "images/icons/iconpersonaleTA.png";
        ruoloStr = "Personale Tecnico Amministrativo";
    }
%>

<!DOCTYPE html>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <title>Il mio Account - UniClass</title>
    <link rel="stylesheet" type="text/css" href="${pageContext.request.contextPath}/styles/headerStyle.css">
    <link rel="stylesheet" type="text/css" href="${pageContext.request.contextPath}/styles/barraNavigazioneStyle.css">
    <link rel="stylesheet" type="text/css" href="${pageContext.request.contextPath}/styles/footerstyle.css">
    <link rel="stylesheet" type="text/css" href="${pageContext.request.contextPath}/styles/uniClassAdd.css">

    <style>
        .account-container {
            max-width: 800px;
            margin: 50px auto;
            background-color: #fff;
            padding: 30px;
            border-radius: 8px;
            box-shadow: 0 4px 6px rgba(0,0,0,0.1);
            text-align: center;
        }
        .profile-img {
            width: 150px;
            height: 150px;
            border-radius: 50%;
            margin-bottom: 20px;
            object-fit: cover;
            border: 4px solid #0056b3;
        }
        .info-group {
            margin: 15px 0;
            padding: 10px;
            border-bottom: 1px solid #eee;
            text-align: left;
        }
        .info-label {
            font-weight: bold;
            color: #555;
            display: block;
            margin-bottom: 5px;
        }
        .info-value {
            font-size: 1.1em;
            color: #333;
        }
    </style>
</head>
<body>

<jsp:include page="header.jsp" />

<div class="content">
    <div class="account-container">
        <img src="<%=request.getContextPath()%>/<%=userIcon%>" alt="Profile Picture" class="profile-img">

        <h2><%= u.getNome() %> <%= u.getCognome() %></h2>
        <p style="color: #666; font-size: 1.2em;"><%= ruoloStr %></p>

        <div class="info-group">
            <span class="info-label">Email Istituzionale</span>
            <span class="info-value"><%= u.getEmail() %></span>
        </div>

        <div class="info-group">
            <span class="info-label">Telefono</span>
            <span class="info-value"><%= (u.getTelefono() != null) ? u.getTelefono() : "Non specificato" %></span>
        </div>

        <% if (isAccademico && acc != null) { %>
        <div class="info-group">
            <span class="info-label">Matricola</span>
            <span class="info-value"><%= acc.getMatricola() %></span>
        </div>

        <div class="info-group">
            <span class="info-label">Dipartimento</span>
            <span class="info-value"><%= (acc.getDipartimento() != null) ? acc.getDipartimento() : "N/D" %></span>
        </div>

        <% if (acc.getCorsoLaurea() != null) { %>
        <div class="info-group">
            <span class="info-label">Corso di Laurea</span>
            <span class="info-value"><%= acc.getCorsoLaurea().getNome() %></span>
        </div>
        <% } %>
        <% } %>

        <br>
        <a href="Logout" class="button" style="background-color: #dc3545;">Disconnetti</a>
    </div>
</div>

<jsp:include page="footer.jsp" />

</body>
</html>
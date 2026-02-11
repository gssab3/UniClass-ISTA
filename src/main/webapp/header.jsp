<%@ page import="it.unisa.uniclass.utenti.model.Utente" %>
<%@ page import="it.unisa.uniclass.utenti.model.Accademico" %>
<%@ page import="it.unisa.uniclass.utenti.model.Ruolo" %>
<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>

<%
    HttpSession sessione = request.getSession(false);

    Utente u = null;
    Accademico acc = null;
    boolean isAccademico = false;

    if (sessione != null) {
        u = (Utente) sessione.getAttribute("currentSessionUser");
        if (u instanceof Accademico) {
            acc = (Accademico) u;
            isAccademico = true;
        }
    }
%>

<header>

    <div class="logo">
        <div class="TastoMenu" onclick="openNav()" align="left">
            <img src="<%=request.getContextPath()%>/images/icons/menuClosedIcon.png" alt="Menu" style="width: 30px; height: 30px; cursor: pointer;">
        </div>
        <a href="<%=request.getContextPath()%>/Home">
            <img src="<%=request.getContextPath()%>/images/logois.png" alt="UniClass Logo">
        </a>
    </div>

    <div class="user-info">
        <div class="user-details">

            <% if (u != null) { %>
            <span class="user-name"><%= u.getNome() %> <%= u.getCognome() %></span>

            <span class="user-role">
                    <% if (isAccademico) { %>
                        <%= acc.getRuolo().toString() %>
                    <% } else { %>
                        Personale TA
                    <% } %>
                </span>

            <% } else { %>
            <span class="user-name">Ospite</span>
            <% } %>

        </div>

        <div class="user-icon">
            <% if (u == null) { %>
            <img src="<%=request.getContextPath()%>/images/icons/usericonnolog.png" alt="User Icon">
            <% } else if (isAccademico && acc.getRuolo() == Ruolo.DOCENTE) { %>
            <img src="<%=request.getContextPath()%>/images/icons/iconprof.png" alt="Docente Icon">
            <% } else if (isAccademico && acc.getRuolo() == Ruolo.STUDENTE) { %>
            <img src="<%=request.getContextPath()%>/images/icons/iconstudent.png" alt="Studente Icon">
            <% } else { %>
            <img src="<%=request.getContextPath()%>/images/icons/iconpersonaleTA.png" alt="PTA Icon">
            <% } %>
        </div>

        <% if (u != null) { %>
        <a href="<%=request.getContextPath()%>/LogoutServlet" class="logout-button">Esci</a>
        <% } %>

    </div>
</header>

package it.unisa.uniclass.testing.unit.utenti.controller;

import it.unisa.uniclass.common.exceptions.AuthenticationException;
import it.unisa.uniclass.utenti.controller.LoginServlet;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.servlet.ServletContext;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.io.IOException;
import java.lang.reflect.Field;

import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class LoginServletTest {

    private LoginServlet servlet;

    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

    @Mock
    private HttpSession session;

    @Mock
    private ServletContext servletContext;

    @Mock
    private UserDirectory userDirectory;

    @BeforeEach
    void setUp() throws Exception {
        servlet = new LoginServlet();

        // Iniezione manuale del Mock @EJB (reflection)
        Field field = LoginServlet.class.getDeclaredField("userDirectory");
        field.setAccessible(true);
        field.set(servlet, userDirectory);

        // Setup base comune
        lenient().when(request.getContextPath()).thenReturn("/ctx");
        lenient().when(request.getSession(true)).thenReturn(session);
        lenient().when(request.getServletContext()).thenReturn(servletContext);
    }

    @Test
    @DisplayName("Login Successo: Accademico Attivato")
    void testLoginSuccess_AccademicoActivated() throws AuthenticationException, IOException {
        // Arrange
        String email = "prof@unisa.it";
        String pwd = "password";
        Accademico acc = new Accademico();
        acc.setEmail(email);
        acc.setAttivato(true); // Fondamentale

        when(request.getParameter("email")).thenReturn(email);
        when(request.getParameter("password")).thenReturn(pwd);
        when(userDirectory.login(email, pwd)).thenReturn(acc);

        // Act
        servlet.doPost(request, response);

        // Assert
        verify(session).setAttribute("currentSessionUser", acc);
        verify(session).setAttribute("utenteEmail", email);
        verify(response).sendRedirect("/ctx/Home");
    }

    @Test
    @DisplayName("Login Fallito: Accademico NON Attivato")
    void testLoginFailure_AccademicoNotActivated() throws AuthenticationException, IOException {
        // Arrange
        String email = "studente@unisa.it";
        Accademico acc = new Accademico();
        acc.setAttivato(false); // Caso da testare

        when(request.getParameter("email")).thenReturn(email);
        when(request.getParameter("password")).thenReturn("pwd");
        when(userDirectory.login(email, "pwd")).thenReturn(acc);

        // Act
        servlet.doPost(request, response);

        // Assert
        verify(response).sendRedirect("/ctx/Login.jsp?action=notactivated");
        // Verifica che NON sia stato creato l'utente in sessione
        verify(session, never()).setAttribute(eq("currentSessionUser"), any());
    }

    @Test
    @DisplayName("Login Successo: Utente Generico (ex PersonaleTA)")
    void testLoginSuccess_GenericUser() throws AuthenticationException, IOException {
        // Arrange
        String email = "admin@unisa.it";
        Utente utente = new Utente(); // Utente semplice, non Accademico
        utente.setEmail(email);

        when(request.getParameter("email")).thenReturn(email);
        when(request.getParameter("password")).thenReturn("pwd");
        when(userDirectory.login(email, "pwd")).thenReturn(utente);

        // Act
        servlet.doPost(request, response);

        // Assert
        // Deve fare il redirect alla home, saltando il check "isAttivato"
        verify(response).sendRedirect("/ctx/Home");
    }

    @Test
    @DisplayName("Login Fallito: AuthenticationException")
    void testLoginFailure_AuthenticationException() throws AuthenticationException, IOException {
        // Arrange
        when(request.getParameter("email")).thenReturn("wrong@unisa.it");
        when(request.getParameter("password")).thenReturn("wrong");
        when(userDirectory.login(anyString(), anyString()))
                .thenThrow(new AuthenticationException("Credenziali errate"));

        // Act
        servlet.doPost(request, response);

        // Assert
        verify(response).sendRedirect("/ctx/Login.jsp?action=error");
    }

    @Test
    @DisplayName("DoGet delegato a DoPost")
    void testDoGet() throws IOException {
        // Spy parziale per verificare la chiamata interna (opzionale, ma utile)
        // Qui testiamo semplicemente che doGet esegua la logica (es. redirect di errore se params null)

        // Simuliamo parametri nulli che causano errore nel doPost -> redirect errore
        when(request.getParameter("email")).thenReturn(null);

        // Se userDirectory.login viene chiamato con null lancia eccezione o gestiamo prima?
        // Nel codice attuale: request.getParameter restituisce null -> login(null, null)
        // Assumiamo che il service o il try catch gestisca.
        // Simuliamo eccezione per brevità o verifichiamo il comportamento safe.
        try {
            when(userDirectory.login(null, null)).thenThrow(new AuthenticationException(""));
        } catch (AuthenticationException e) { /* ignore setup */ }

        servlet.doGet(request, response);

        verify(response).sendRedirect(contains("Login.jsp?action=error"));
    }

    @Test
    @DisplayName("Gestione IOException del Servlet")
    void testIOExceptionHandling() throws IOException {
        // Arrange
        when(request.getParameter("email")).thenReturn("io@test.it");
        when(request.getParameter("password")).thenReturn("pwd");

        Utente u = new Utente();
        u.setEmail("io@test.it");
        when(userDirectory.login(anyString(), anyString())).thenReturn(u);

        // Facciamo lanciare IOException alla prima redirect (o al getSession)
        doThrow(new IOException("Simulated IO Error")).when(response).sendRedirect(anyString());

        // Act
        servlet.doPost(request, response);

        // Assert
        // Verifica che l'errore sia stato loggato
        verify(servletContext).log(eq("Error processing login request"), any(IOException.class));
    }
}
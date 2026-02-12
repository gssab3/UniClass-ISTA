package it.unisa.uniclass.testing.unit.utenti.controller;

import it.unisa.uniclass.utenti.controller.GetEmailServlet;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.servlet.ServletContext;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.reflect.Field;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class GetEmailServletTest {

    // Wrapper per esporre i metodi protected
    static class TestableGetEmailServlet extends GetEmailServlet {
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp) {
            super.doGet(req, resp);
        }

        @Override
        public void doPost(HttpServletRequest req, HttpServletResponse resp) {
            super.doPost(req, resp);
        }
    }

    private TestableGetEmailServlet servlet;

    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

    @Mock
    private UserDirectory userDirectory;

    @Mock
    private ServletContext servletContext;

    private StringWriter stringWriter;
    private PrintWriter printWriter;

    @BeforeEach
    void setUp() throws Exception {
        servlet = new TestableGetEmailServlet();

        // Iniezione manuale del Mock via Reflection
        Field field = GetEmailServlet.class.getDeclaredField("userDirectory");
        field.setAccessible(true);
        field.set(servlet, userDirectory);

        // Setup Response Writer
        stringWriter = new StringWriter();
        printWriter = new PrintWriter(stringWriter);
        lenient().when(response.getWriter()).thenReturn(printWriter);

        // Setup Context
        lenient().when(request.getServletContext()).thenReturn(servletContext);
    }

    @Test
    @DisplayName("DoGet: Restituisce lista email in JSON")
    void testDoGetWithEmails() {
        // Arrange
        Utente u1 = new Utente(); u1.setEmail("a@unisa.it");
        Utente u2 = new Utente(); u2.setEmail("b@unisa.it");
        List<Utente> utenti = Arrays.asList(u1, u2);

        when(userDirectory.getTuttiGliUtenti()).thenReturn(utenti);

        // Act
        servlet.doGet(request, response);

        // Assert
        String output = stringWriter.toString();

        // Verifica contenuto
        assertTrue(output.contains("a@unisa.it"));
        assertTrue(output.contains("b@unisa.it"));

        // Verifica Headers
        verify(response).setContentType("application/json");
        verify(response).setCharacterEncoding("UTF-8");
    }

    @Test
    @DisplayName("DoGet: Lista vuota")
    void testDoGetEmpty() {
        when(userDirectory.getTuttiGliUtenti()).thenReturn(Collections.emptyList());

        servlet.doGet(request, response);

        String output = stringWriter.toString();
        // A seconda dell'impl, potrebbe essere "[]" o un array vuoto
        assertTrue(output.contains("[]") || output.trim().isEmpty());
    }

    @Test
    @DisplayName("DoGet: Gestione Eccezioni (Log e 500)")
    void testDoGetWithException() throws IOException {
        // Arrange
        when(userDirectory.getTuttiGliUtenti()).thenThrow(new RuntimeException("Errore simulato"));

        // Act
        servlet.doGet(request, response);

        // Assert
        verify(response).setStatus(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        verify(response).getWriter();
    }

    @Test
    @DisplayName("DoPost: Delega a DoGet")
    void testDoPostDelegatesToDoGet() {
        // Arrange
        Utente u = new Utente(); u.setEmail("post@unisa.it");
        when(userDirectory.getTuttiGliUtenti()).thenReturn(Collections.singletonList(u));

        // Act
        servlet.doPost(request, response);

        // Assert
        String output = stringWriter.toString();
        assertTrue(output.contains("post@unisa.it"));
        verify(userDirectory).getTuttiGliUtenti(); // Conferma che la logica è stata chiamata
    }
}
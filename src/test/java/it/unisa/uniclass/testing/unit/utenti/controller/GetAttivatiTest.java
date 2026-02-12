package it.unisa.uniclass.testing.unit.utenti.controller;

import it.unisa.uniclass.utenti.controller.GetAttivati;
import it.unisa.uniclass.utenti.model.Accademico;
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
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class GetAttivatiTest {

    // Wrapper per esporre i metodi protected
    static class TestableGetAttivati extends GetAttivati {
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp) {
            super.doGet(req, resp);
        }

        @Override
        public void doPost(HttpServletRequest req, HttpServletResponse resp) {
            super.doPost(req, resp);
        }
    }

    private TestableGetAttivati servlet;

    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

    @Mock
    private UserDirectory userDirectory;

    @Mock
    private ServletContext servletContext;

    @BeforeEach
    void setUp() throws Exception {
        servlet = new TestableGetAttivati();

        // Iniezione manuale del Mock via Reflection
        Field field = GetAttivati.class.getDeclaredField("userDirectory");
        field.setAccessible(true);
        field.set(servlet, userDirectory);

        // Setup base per il logging
        lenient().when(request.getServletContext()).thenReturn(servletContext);
    }

    @Test
    @DisplayName("DoGet: Restituisce JSON corretto filtrando solo Accademici Attivati")
    void testDoGet_Success() throws IOException {
        // 1. Arrange - Creiamo scenari misti

        // Accademico Attivato (Deve esserci)
        Accademico acc1 = new Accademico();
        acc1.setEmail("attivo@unisa.it");
        acc1.setAttivato(true);

        // Accademico NON Attivato (Non deve esserci)
        Accademico acc2 = new Accademico();
        acc2.setEmail("inattivo@unisa.it");
        acc2.setAttivato(false);

        // Utente Generico (Non deve esserci)
        Utente simpleUser = new Utente();
        simpleUser.setEmail("admin@unisa.it");

        List<Utente> listaUtenti = Arrays.asList(acc1, acc2, simpleUser);
        when(userDirectory.getTuttiGliUtenti()).thenReturn(listaUtenti);

        // Cattura dell'output
        StringWriter stringWriter = new StringWriter();
        PrintWriter writer = new PrintWriter(stringWriter);
        when(response.getWriter()).thenReturn(writer);

        // 2. Act
        servlet.doGet(request, response);

        // 3. Assert
        verify(response).setContentType("application/json");
        verify(response).setCharacterEncoding("UTF-8");

        String jsonOutput = stringWriter.toString();

        // Verifica che contenga l'email attiva
        assertTrue(jsonOutput.contains("attivo@unisa.it"), "Il JSON deve contenere l'utente attivato");

        // Verifica che NON contenga l'email inattiva
        assertFalse(jsonOutput.contains("inattivo@unisa.it"), "Il JSON non deve contenere l'utente non attivato");

        // Verifica che NON contenga l'utente generico
        assertFalse(jsonOutput.contains("admin@unisa.it"), "Il JSON non deve contenere utenti non accademici");

        // Verifica struttura JSON Array
        assertTrue(jsonOutput.startsWith("[") && jsonOutput.endsWith("]"));
    }

    @Test
    @DisplayName("DoGet: Lista vuota restituisce Array vuoto")
    void testDoGet_EmptyList() throws IOException {
        when(userDirectory.getTuttiGliUtenti()).thenReturn(Collections.emptyList());

        StringWriter stringWriter = new StringWriter();
        when(response.getWriter()).thenReturn(new PrintWriter(stringWriter));

        servlet.doGet(request, response);

        assertEquals("[]", stringWriter.toString());
    }

    @Test
    @DisplayName("DoPost: Delega a DoGet")
    void testDoPost_Delegates() throws IOException {
        // Setup minimo per garantire che doGet venga eseguito senza errori
        when(userDirectory.getTuttiGliUtenti()).thenReturn(Collections.emptyList());
        when(response.getWriter()).thenReturn(new PrintWriter(new StringWriter()));

        servlet.doPost(request, response);

        // Verifica che userDirectory sia stato chiamato (prova che doGet è partito)
        verify(userDirectory).getTuttiGliUtenti();
    }

    @Test
    @DisplayName("Gestione Eccezioni: Log e 500")
    void testExceptionHandling() throws IOException {
        // Forziamo un'eccezione nel service
        when(userDirectory.getTuttiGliUtenti()).thenThrow(new RuntimeException("Database down"));

        servlet.doGet(request, response);

        // Verifica log
        verify(servletContext).log(eq("Error processing GetAttivati"), any(RuntimeException.class));

        // Verifica risposta errore http
        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
    }
}